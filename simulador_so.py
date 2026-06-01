"""
Simulador de Gerenciador e Escalonador de Processos
====================================================
Implementa:
  - Gerenciamento de Memória: First-Fit com split e merge
  - Escalonamento de Tempo Real: FCFS com prioridade absoluta e preempção de usuário
  - Escalonamento de Usuário: MLFQ com 3 filas de feedback, quantum = 2 u.t.
  - Interface gráfica Tkinter com visualização em tempo real
  - Logs completos de transições de estado

Resposta Teórica sobre Threads (Requisito 7.3):
-------------------------------------------------
O simulador poderia se beneficiar de múltiplas threads das seguintes formas:

1. SEPARAÇÃO LÓGICA: Cada CPU simulada poderia ser representada por uma thread
   real do sistema operacional hospedeiro, executando em paralelo e refletindo
   de forma mais fiel o comportamento de um hardware multiprocessado real.

2. DESACOPLAMENTO GUI/LÓGICA: A thread principal cuida exclusivamente da
   interface gráfica (loop de eventos Tkinter), enquanto uma thread secundária
   executa os ticks da simulação. Isso evita que a GUI "congele" durante
   processamentos pesados, tornando a interface sempre responsiva.

3. I/O ASSÍNCRONO: Os 4 discos simulados poderiam cada um ter sua própria
   thread gerenciando contagens regressivas de I/O em paralelo, eliminando
   o gargalo do loop serial atual.

4. PREEMPÇÃO REAL: Uma thread de monitor de prioridade poderia observar
   continuamente as filas RT e disparar preempções imediatas, sem esperar
   o próximo tick, aproximando a simulação de um escalonador preemptivo real.

CUIDADOS: O uso de threads exigiria mecanismos de sincronização (Locks,
Semaphores ou Queue thread-safe) para proteger as estruturas de dados
compartilhadas (filas de processos, estado das CPUs/discos, lista de blocos
de memória) contra condições de corrida (race conditions), que são o principal
risco em sistemas concorrentes.
"""

import tkinter as tk
from tkinter import filedialog, messagebox
import os


# =============================================================================
# ENTIDADES
# =============================================================================

class MemoryBlock:
    """Representa um bloco contíguo de memória (livre ou alocado)."""
    def __init__(self, start, size, free=True, pid=None):
        self.start = start
        self.size  = size
        self.free  = free
        self.pid   = pid


class Process:
    """
    Representa um processo com suas fases de execução.
    Regra de tipo:
      - Tempo Real (RT) : io == 0  AND  cpu2 == 0  AND  ram <= 512 MiB
      - Usuário  (USER) : qualquer outro caso
    """
    def __init__(self, pid, cpu1, io, cpu2, ram):
        self.pid  = pid
        self.ram  = ram

        # Durações originais (para exibição)
        self.cpu1_total = cpu1
        self.io_total   = io
        self.cpu2_total = cpu2

        # Contadores restantes (decrementados durante execução)
        self.cpu1_rem = cpu1
        self.io_rem   = io
        self.cpu2_rem = cpu2

        # Tipo e prioridade
        if io == 0 and cpu2 == 0 and ram <= 512:
            self.ptype    = 'RT'
            self.priority = 0
        else:
            self.ptype    = 'USER'
            self.priority = 1

        # Máquina de estados
        self.state = 'NEW'
        # Fases: 'CPU1' | 'IO' | 'CPU2' | 'DONE'
        self.phase = 'CPU1'

        # Controle MLFQ (apenas para USER)
        self.queue_level  = 0
        self.quantum_used = 0

        # Referência ao recurso em uso
        self.cpu_id  = None
        self.disk_id = None


# =============================================================================
# GERENCIADOR DE MEMÓRIA
# =============================================================================

class MemoryManager:
    """
    Gerencia a memória principal usando First-Fit com split e merge.
    Tamanho padrão: 32 GiB = 32768 MiB.
    """
    def __init__(self, total_mib=32768):
        self.total = total_mib
        self.blocks = [MemoryBlock(0, total_mib)]

    def allocate(self, pid, size):
        """
        Tenta alocar 'size' MiB para o processo 'pid'.
        Retorna True em sucesso, False se não houver bloco livre suficiente.
        """
        for i, blk in enumerate(self.blocks):
            if blk.free and blk.size >= size:
                if blk.size > size:
                    # Split: cria fragmento livre após o bloco alocado
                    remainder = MemoryBlock(blk.start + size, blk.size - size)
                    self.blocks.insert(i + 1, remainder)
                blk.size = size
                blk.free = False
                blk.pid  = pid
                return True
        return False

    def deallocate(self, pid):
        """Libera o bloco alocado ao processo 'pid' e faz merge de adjacentes livres."""
        for blk in self.blocks:
            if blk.pid == pid:
                blk.free = True
                blk.pid  = None
                self._merge()
                return True
        return False

    def _merge(self):
        """Fusão (coalescing) de blocos livres adjacentes."""
        i = 0
        while i < len(self.blocks) - 1:
            if self.blocks[i].free and self.blocks[i + 1].free:
                self.blocks[i].size += self.blocks[i + 1].size
                del self.blocks[i + 1]
            else:
                i += 1

    def snapshot(self):
        """Retorna lista de tuplas (start, size, free, pid) para exibição."""
        return [(b.start, b.size, b.free, b.pid) for b in self.blocks]


# =============================================================================
# NÚCLEO DO SIMULADOR
# =============================================================================

class OSSimulator:
    """
    Núcleo da simulação. Cada chamada a tick() avança 1 unidade de tempo.

    Ordem causal correta dentro de um tick:
      1. Admissão  : tenta alocar memória para processos ainda não admitidos
      2. Execução CPU  : decrementa contadores, detecta fim de fase / preempção
      3. Execução I/O  : decrementa contadores de disco, detecta fim de I/O
      4. Despacho I/O  : move processos da fila IO_WAIT para discos livres
      5. Preempção RT  : se houver processo RT na fila e todas as CPUs ocupadas
                         por USER, expulsa o USER de menor prioridade de fila
      6. Despacho CPU  : preenche CPUs livres respeitando RT > U0 > U1 > U2
    """

    QUANTUM = 2  # Quantum de tempo para processos de Usuário

    def __init__(self):
        self.memory = MemoryManager()
        self.cpus   = [None] * 4
        self.disks  = [None] * 4

        # Fila de entrada (ainda sem memória alocada)
        self.unadmitted = []

        # Filas de prontos / espera
        self.rt_queue   = []        # Tempo Real — FCFS
        self.mlfq       = [[], [], []]  # Usuário — 3 níveis de feedback
        self.io_wait    = []        # Aguardando disco

        self.clock = 0
        self.logs  = []             # Histórico completo de eventos
        self.finished = []          # Processos finalizados (para estatísticas)
        self.simulation_done = False

    # ------------------------------------------------------------------
    # INTERFACE PÚBLICA
    # ------------------------------------------------------------------

    def load_from_file(self, filepath):
        """Lê o arquivo de processos e popula unadmitted."""
        with open(filepath, 'r') as f:
            for line in f:
                line = line.strip().replace('[', '').replace(']', '')
                if not line:
                    continue
                try:
                    parts = [int(x.strip()) for x in line.split(',')]
                    if len(parts) != 5:
                        continue
                    pid, cpu1, io, cpu2, ram = parts
                    proc = Process(pid, cpu1, io, cpu2, ram)
                    self.unadmitted.append(proc)
                    self._log(f"Processo #{pid} lido "
                              f"[{proc.ptype} | CPU1={cpu1} IO={io} CPU2={cpu2} RAM={ram}MiB]")
                except ValueError:
                    self._log(f"Linha malformada ignorada: '{line}'")

    def tick(self):
        """Avança 1 unidade de tempo."""
        if self.simulation_done:
            return

        self.clock += 1
        self._log(f"──── TICK {self.clock} ────")

        # Passos em ordem causal
        self._step_admit()
        self._step_run_cpus()
        self._step_run_disks()
        self._step_dispatch_io()
        self._step_rt_preemption()
        self._step_dispatch_cpus()

        # Verifica término
        if self._is_done():
            self.simulation_done = True
            self._log(f"✔ SIMULAÇÃO CONCLUÍDA no Tick {self.clock}")

    def is_active(self):
        """True enquanto ainda há processos no sistema."""
        return not self._is_done()

    # ------------------------------------------------------------------
    # PASSOS INTERNOS DO TICK
    # ------------------------------------------------------------------

    def _step_admit(self):
        """Tenta admitir processos pendentes alocando memória."""
        admitted = []
        for proc in self.unadmitted:
            if self.memory.allocate(proc.pid, proc.ram):
                self._change_state(proc, 'READY')
                if proc.ptype == 'RT':
                    self.rt_queue.append(proc)
                else:
                    self.mlfq[0].append(proc)
                admitted.append(proc)
                self._log(f"Processo #{proc.pid} admitido na memória "
                          f"(endereço inicial detectado).")
        for proc in admitted:
            self.unadmitted.remove(proc)

    def _step_run_cpus(self):
        """Executa 1 u.t. de CPU para cada processo em execução."""
        for i in range(4):
            proc = self.cpus[i]
            if proc is None:
                continue

            # Decrementa o contador da fase correta
            if proc.phase == 'CPU1':
                proc.cpu1_rem -= 1
                rem = proc.cpu1_rem
            else:  # CPU2
                proc.cpu2_rem -= 1
                rem = proc.cpu2_rem

            # Incrementa quantum apenas para USER
            if proc.ptype == 'USER':
                proc.quantum_used += 1

            self._log(f"[CPU {i}] PID #{proc.pid} ({proc.ptype}) "
                      f"fase={proc.phase} restante={rem} "
                      f"quantum={proc.quantum_used}/{self.QUANTUM}")

            # --- Caso A: fase concluída ---
            if rem == 0:
                self.cpus[i] = None
                proc.cpu_id = None
                self._on_cpu_phase_done(proc)

            # --- Caso B: estouro de quantum (somente USER) ---
            elif proc.ptype == 'USER' and proc.quantum_used >= self.QUANTUM:
                self.cpus[i] = None
                proc.cpu_id    = None
                proc.quantum_used = 0
                # Rebaixamento na fila de feedback
                proc.queue_level = min(2, proc.queue_level + 1)
                self._change_state(proc, 'READY')
                self.mlfq[proc.queue_level].append(proc)
                self._log(f"⚡ Preempção de quantum: PID #{proc.pid} "
                          f"rebaixado para fila U{proc.queue_level}.")

    def _on_cpu_phase_done(self, proc):
        """Trata o fim de uma fase de CPU."""
        if proc.phase == 'CPU1':
            if proc.io_total > 0:
                # Há fase de I/O: bloqueia
                proc.phase = 'IO'
                proc.io_rem = proc.io_total  # garante valor correto
                self._change_state(proc, 'BLOCKED')
                self.io_wait.append(proc)
                self._log(f"Processo #{proc.pid} bloqueado aguardando I/O.")
            else:
                # Sem I/O (e cpu2 == 0 por definição de RT puro)
                self._finalize(proc)
        else:  # CPU2
            self._finalize(proc)

    def _step_run_disks(self):
        """Executa 1 u.t. de I/O para cada processo nos discos."""
        for i in range(4):
            proc = self.disks[i]
            if proc is None:
                continue

            proc.io_rem -= 1
            self._log(f"[DISCO {i}] PID #{proc.pid} I/O restante={proc.io_rem}")

            if proc.io_rem == 0:
                self.disks[i] = None
                proc.disk_id = None

                if proc.cpu2_total > 0:
                    # Retorna para fila U0 (recompensa por ser I/O-bound)
                    proc.phase = 'CPU2'
                    proc.cpu2_rem = proc.cpu2_total
                    proc.queue_level = 0
                    proc.quantum_used = 0
                    self._change_state(proc, 'READY')
                    self.mlfq[0].append(proc)
                    self._log(f"Processo #{proc.pid} retornou do I/O → fila U0.")
                else:
                    self._finalize(proc)

    def _step_dispatch_io(self):
        """Aloca discos livres para processos na io_wait (FCFS)."""
        for i in range(4):
            if self.disks[i] is None and self.io_wait:
                proc = self.io_wait.pop(0)
                self.disks[i] = proc
                proc.disk_id = i
                self._log(f"Processo #{proc.pid} alocado no [DISCO {i}].")

    def _step_rt_preemption(self):
        """
        Se há processo RT esperando e não há CPU livre,
        expulsa o processo USER de maior nível de fila (pior prioridade)
        para liberar uma CPU.
        FCFS de RT nunca é interrompido por outro RT.
        """
        if not self.rt_queue:
            return

        free = self._free_cpu()
        if free != -1:
            return  # Há CPU livre; o despacho normal vai cuidar

        # Tenta preemptar o processo USER de pior fila
        victim_cpu = -1
        worst_level = -1
        for i in range(4):
            proc = self.cpus[i]
            if proc is not None and proc.ptype == 'USER':
                if proc.queue_level > worst_level:
                    worst_level = proc.queue_level
                    victim_cpu = i

        if victim_cpu == -1:
            # Todas as CPUs com RT — RT aguarda (sem preempção de RT por RT)
            return

        victim = self.cpus[victim_cpu]
        self.cpus[victim_cpu] = None
        victim.cpu_id = None
        # Mantém quantum_used; o processo volta para o início de sua fila
        self._change_state(victim, 'READY')
        self.mlfq[victim.queue_level].insert(0, victim)
        self._log(f"⚠ PREEMPÇÃO: PID #{victim.pid} (USER/U{victim.queue_level}) "
                  f"expulso da [CPU {victim_cpu}] para ceder lugar ao Tempo Real.")

    def _step_dispatch_cpus(self):
        """
        Preenche CPUs livres na ordem de prioridade:
        RT (FCFS) > U0 > U1 > U2
        """
        for i in range(4):
            if self.cpus[i] is not None:
                continue
            proc = self._next_ready()
            if proc is None:
                continue
            self.cpus[i] = proc
            proc.cpu_id = i
            proc.quantum_used = 0
            self._change_state(proc, 'RUNNING')
            queue_label = 'RT' if proc.ptype == 'RT' else f'U{proc.queue_level}'
            self._log(f"Processo #{proc.pid} [{queue_label}] alocado na [CPU {i}].")

    # ------------------------------------------------------------------
    # AUXILIARES
    # ------------------------------------------------------------------

    def _finalize(self, proc):
        proc.phase = 'DONE'
        self._change_state(proc, 'TERMINATED')
        self.memory.deallocate(proc.pid)
        self.finished.append(proc)
        self._log(f"✓ Processo #{proc.pid} FINALIZADO. Memória liberada.")

    def _change_state(self, proc, new_state):
        if proc.state != new_state:
            self._log(f"Processo #{proc.pid}: de {proc.state} para {new_state}")
            proc.state = new_state

    def _log(self, msg):
        entry = f"[T{self.clock:03d}] {msg}"
        self.logs.append(entry)

    def _free_cpu(self):
        for i in range(4):
            if self.cpus[i] is None:
                return i
        return -1

    def _next_ready(self):
        if self.rt_queue:
            return self.rt_queue.pop(0)
        for level in range(3):
            if self.mlfq[level]:
                return self.mlfq[level].pop(0)
        return None

    def _is_done(self):
        return (not self.unadmitted and
                not self.rt_queue and
                not any(self.mlfq) and
                not self.io_wait and
                not any(self.cpus) and
                not any(self.disks))


# =============================================================================
# INTERFACE GRÁFICA
# =============================================================================

# Paleta: tema terminal retro-futurista (fundo escuro, verde fosforescente)
C_BG        = "#0D1117"   # fundo geral
C_PANEL     = "#161B22"   # fundo de painéis
C_BORDER    = "#30363D"   # bordas
C_GREEN     = "#39D353"   # acento verde (ativo/livre)
C_ORANGE    = "#F0883E"   # acento laranja (processo USER)
C_CYAN      = "#58A6FF"   # acento azul/ciano (processo RT)
C_RED       = "#FF7B72"   # acento vermelho (bloqueado/erro)
C_YELLOW    = "#E3B341"   # acento amarelo (aviso/quantum)
C_TEXT      = "#C9D1D9"   # texto primário
C_MUTED     = "#8B949E"   # texto secundário
C_FONT_MONO = ("Courier New", 9)
C_FONT_BODY = ("Courier New", 10)
C_FONT_HEAD = ("Courier New", 11, "bold")
C_FONT_BIG  = ("Courier New", 14, "bold")


class AppGUI:
    AUTO_SPEED_MS = 600  # milissegundos entre ticks automáticos

    def __init__(self, root):
        self.root = root
        self.root.title("OS Process Scheduler Simulator")
        self.root.configure(bg=C_BG)
        self.root.minsize(1100, 750)

        self.sim     = OSSimulator()
        self.running = False
        self._after_id = None

        self._build_gui()
        self._refresh()

    # ------------------------------------------------------------------
    # CONSTRUÇÃO DA GUI
    # ------------------------------------------------------------------

    def _build_gui(self):
        # ── Cabeçalho ──────────────────────────────────────────────────
        hdr = tk.Frame(self.root, bg=C_BG)
        hdr.pack(fill=tk.X, padx=16, pady=(14, 4))

        tk.Label(hdr, text="OS SCHEDULER SIMULATOR",
                 font=("Courier New", 18, "bold"),
                 fg=C_GREEN, bg=C_BG).pack(side=tk.LEFT)

        self.lbl_clock = tk.Label(hdr, text="TICK  000",
                                  font=C_FONT_BIG, fg=C_YELLOW, bg=C_BG)
        self.lbl_clock.pack(side=tk.RIGHT)

        # ── Barra de controles ─────────────────────────────────────────
        ctrl = tk.Frame(self.root, bg=C_PANEL, bd=0,
                        highlightthickness=1, highlightbackground=C_BORDER)
        ctrl.pack(fill=tk.X, padx=16, pady=4)

        self._btn("📂 Carregar Arquivo", self._load_file, ctrl, C_CYAN)
        self._btn("▶  Iniciar",          self._start,     ctrl, C_GREEN)
        self._btn("⏸  Pausar",           self._pause,     ctrl, C_YELLOW)
        self._btn("⏭  +1 Tick",          self._step,      ctrl, C_ORANGE)
        self._btn("↺  Reiniciar",         self._reset,     ctrl, C_RED)

        self.lbl_status = tk.Label(ctrl, text="● Aguardando arquivo...",
                                   font=C_FONT_BODY, fg=C_MUTED, bg=C_PANEL)
        self.lbl_status.pack(side=tk.RIGHT, padx=12)

        # ── Layout principal (duas colunas) ────────────────────────────
        body = tk.Frame(self.root, bg=C_BG)
        body.pack(fill=tk.BOTH, expand=True, padx=16, pady=4)
        body.columnconfigure(0, weight=3)
        body.columnconfigure(1, weight=2)
        body.rowconfigure(0, weight=1)

        left  = tk.Frame(body, bg=C_BG)
        right = tk.Frame(body, bg=C_BG)
        left.grid(row=0, column=0, sticky="nsew", padx=(0, 6))
        right.grid(row=0, column=1, sticky="nsew")

        # ── Coluna Esquerda ────────────────────────────────────────────
        # CPUs
        cpu_frame = self._panel(left, "⚙  CPUs (4 núcleos)")
        cpu_frame.pack(fill=tk.X, pady=(0, 6))
        self.cpu_bars = []
        for i in range(4):
            row = tk.Frame(cpu_frame, bg=C_PANEL)
            row.pack(fill=tk.X, pady=2)
            lbl = tk.Label(row, text=f"CPU {i}", font=C_FONT_MONO,
                           fg=C_MUTED, bg=C_PANEL, width=6, anchor='w')
            lbl.pack(side=tk.LEFT, padx=(0, 6))
            bar = tk.Label(row, text="── LIVRE ──", font=C_FONT_MONO,
                           fg=C_MUTED, bg=C_BG, anchor='w',
                           relief='flat', padx=6, pady=3)
            bar.pack(side=tk.LEFT, fill=tk.X, expand=True)
            self.cpu_bars.append(bar)

        # Discos
        disk_frame = self._panel(left, "💿  Discos I/O (4 unidades)")
        disk_frame.pack(fill=tk.X, pady=(0, 6))
        self.disk_bars = []
        for i in range(4):
            row = tk.Frame(disk_frame, bg=C_PANEL)
            row.pack(fill=tk.X, pady=2)
            lbl = tk.Label(row, text=f"DSK {i}", font=C_FONT_MONO,
                           fg=C_MUTED, bg=C_PANEL, width=6, anchor='w')
            lbl.pack(side=tk.LEFT, padx=(0, 6))
            bar = tk.Label(row, text="── LIVRE ──", font=C_FONT_MONO,
                           fg=C_MUTED, bg=C_BG, anchor='w',
                           relief='flat', padx=6, pady=3)
            bar.pack(side=tk.LEFT, fill=tk.X, expand=True)
            self.disk_bars.append(bar)

        # Filas
        q_frame = self._panel(left, "📋  Filas de Prontos / Espera")
        q_frame.pack(fill=tk.X, pady=(0, 6))
        self.q_labels = {}
        queue_defs = [
            ('rt',   'RT   (Tempo Real / FCFS)', C_CYAN),
            ('u0',   'U0   (Usuário / Prioridade Alta)',  C_ORANGE),
            ('u1',   'U1   (Usuário / Média)',   C_ORANGE),
            ('u2',   'U2   (Usuário / Baixa)',   C_ORANGE),
            ('io',   'I/O  (Aguardando Disco)',  C_RED),
            ('new',  'NEW  (Aguardando Memória)',C_YELLOW),
        ]
        for key, label, color in queue_defs:
            row = tk.Frame(q_frame, bg=C_PANEL)
            row.pack(fill=tk.X, pady=1)
            tk.Label(row, text=label, font=C_FONT_MONO,
                     fg=color, bg=C_PANEL, width=32, anchor='w').pack(side=tk.LEFT)
            lbl = tk.Label(row, text="[]", font=C_FONT_MONO,
                           fg=C_TEXT, bg=C_PANEL, anchor='w')
            lbl.pack(side=tk.LEFT, fill=tk.X, expand=True)
            self.q_labels[key] = lbl

        # ── Coluna Direita ─────────────────────────────────────────────
        # Memória
        mem_outer = self._panel(right, "🧠  Memória Principal (32 GiB — First-Fit)")
        mem_outer.pack(fill=tk.X, pady=(0, 6))

        # Barra visual de memória
        self.mem_canvas = tk.Canvas(mem_outer, height=22, bg=C_BG,
                                    highlightthickness=0)
        self.mem_canvas.pack(fill=tk.X, pady=(0, 4))

        self.mem_list = tk.Text(mem_outer, height=7, font=C_FONT_MONO,
                                bg=C_BG, fg=C_TEXT, relief='flat',
                                state='disabled', wrap='none')
        self.mem_list.pack(fill=tk.BOTH, expand=True)

        # Log
        log_outer = self._panel(right, "📟  Log de Eventos")
        log_outer.pack(fill=tk.BOTH, expand=True)

        self.log_text = tk.Text(log_outer, font=("Courier New", 8),
                                bg=C_BG, fg=C_TEXT, relief='flat',
                                state='disabled', wrap='word')
        log_scroll = tk.Scrollbar(log_outer, command=self.log_text.yview,
                                  bg=C_BORDER, troughcolor=C_BG)
        self.log_text.configure(yscrollcommand=log_scroll.set)
        log_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_text.pack(fill=tk.BOTH, expand=True)

        # Tags de cor no log
        self.log_text.tag_configure('tick',  foreground=C_YELLOW)
        self.log_text.tag_configure('state', foreground=C_CYAN)
        self.log_text.tag_configure('rt',    foreground=C_CYAN)
        self.log_text.tag_configure('preempt', foreground=C_RED)
        self.log_text.tag_configure('done',  foreground=C_GREEN)
        self.log_text.tag_configure('warn',  foreground=C_ORANGE)

    # ------------------------------------------------------------------
    # CONTROLES
    # ------------------------------------------------------------------

    def _load_file(self):
        fp = filedialog.askopenfilename(
            title="Selecionar arquivo de processos",
            filetypes=[("Arquivos de texto", "*.txt"), ("Todos", "*.*")])
        if not fp:
            return
        self._reset()
        try:
            self.sim.load_from_file(fp)
            n = len(self.sim.unadmitted)
            self._set_status(f"● {n} processo(s) carregado(s).", C_GREEN)
        except Exception as e:
            messagebox.showerror("Erro ao carregar", str(e))
            self._set_status("● Erro ao carregar arquivo.", C_RED)
        self._refresh()

    def _start(self):
        if self.sim.simulation_done:
            return
        self.running = True
        self._set_status("● Simulando...", C_GREEN)
        self._auto_tick()

    def _pause(self):
        self.running = False
        if self._after_id:
            self.root.after_cancel(self._after_id)
            self._after_id = None
        self._set_status("● Pausado.", C_YELLOW)

    def _step(self):
        if self.sim.simulation_done:
            return
        self._pause()
        self._do_tick()

    def _reset(self):
        self._pause()
        self.sim = OSSimulator()
        self._set_status("● Aguardando arquivo...", C_MUTED)
        self._refresh()

    def _auto_tick(self):
        if not self.running:
            return
        if self.sim.simulation_done:
            self.running = False
            self._set_status(f"✔ Concluído no Tick {self.sim.clock}!", C_GREEN)
            return
        self._do_tick()
        self._after_id = self.root.after(self.AUTO_SPEED_MS, self._auto_tick)

    def _do_tick(self):
        self.sim.tick()
        self._refresh()
        if self.sim.simulation_done:
            self.running = False
            self._set_status(f"✔ Concluído no Tick {self.sim.clock}!", C_GREEN)

    # ------------------------------------------------------------------
    # ATUALIZAÇÃO DOS WIDGETS
    # ------------------------------------------------------------------

    def _refresh(self):
        self.lbl_clock.config(text=f"TICK  {self.sim.clock:03d}")
        self._refresh_cpus()
        self._refresh_disks()
        self._refresh_queues()
        self._refresh_memory()
        self._refresh_log()

    def _refresh_cpus(self):
        for i, bar in enumerate(self.cpu_bars):
            proc = self.sim.cpus[i]
            if proc is None:
                bar.config(text="── LIVRE ──", fg=C_MUTED, bg=C_BG)
            else:
                color  = C_CYAN if proc.ptype == 'RT' else C_ORANGE
                phase  = proc.phase
                if phase == 'CPU1':
                    rem = proc.cpu1_rem
                else:
                    rem = proc.cpu2_rem
                qinfo = f"  Q:{proc.quantum_used}/{OSSimulator.QUANTUM}" if proc.ptype == 'USER' else ""
                bar.config(
                    text=f"PID #{proc.pid:>3}  [{proc.ptype}]  {phase}  rem={rem}{qinfo}",
                    fg=color, bg="#1A2035")

    def _refresh_disks(self):
        for i, bar in enumerate(self.disk_bars):
            proc = self.sim.disks[i]
            if proc is None:
                bar.config(text="── LIVRE ──", fg=C_MUTED, bg=C_BG)
            else:
                bar.config(
                    text=f"PID #{proc.pid:>3}  [I/O]  rem={proc.io_rem}",
                    fg=C_RED, bg="#1A1A2E")

    def _refresh_queues(self):
        def pids(lst):
            if not lst:
                return "[]"
            return "[" + "  ".join(f"#{p.pid}" for p in lst) + "]"

        self.q_labels['rt'].config(text=pids(self.sim.rt_queue))
        self.q_labels['u0'].config(text=pids(self.sim.mlfq[0]))
        self.q_labels['u1'].config(text=pids(self.sim.mlfq[1]))
        self.q_labels['u2'].config(text=pids(self.sim.mlfq[2]))
        self.q_labels['io'].config(text=pids(self.sim.io_wait))
        self.q_labels['new'].config(text=pids(self.sim.unadmitted))

    def _refresh_memory(self):
        # Barra visual
        canvas = self.mem_canvas
        canvas.delete("all")
        w = canvas.winfo_width() or 400
        total = self.sim.memory.total

        for blk in self.sim.memory.blocks:
            x0 = int(blk.start / total * w)
            x1 = int((blk.start + blk.size) / total * w)
            color = C_GREEN if blk.free else (C_CYAN if self._is_rt_pid(blk.pid) else C_ORANGE)
            canvas.create_rectangle(x0, 2, max(x1 - 1, x0 + 1), 20,
                                    fill=color, outline=C_BG)

        # Lista textual
        self.mem_list.config(state='normal')
        self.mem_list.delete(1.0, tk.END)
        for blk in self.sim.memory.blocks:
            if blk.free:
                line = f"  [LIVRE]  {blk.start:>7} MiB  →  {blk.start + blk.size:>7} MiB  ({blk.size} MiB)\n"
                self.mem_list.insert(tk.END, line, 'free')
            else:
                ptype = self._get_ptype(blk.pid)
                color_tag = 'rt' if ptype == 'RT' else 'user'
                line = f"  PID #{blk.pid:<3}  {blk.start:>7} MiB  →  {blk.start + blk.size:>7} MiB  ({blk.size} MiB)\n"
                self.mem_list.insert(tk.END, line, color_tag)
        self.mem_list.config(state='disabled')

        # Tags de cor
        self.mem_list.tag_configure('free', foreground=C_GREEN)
        self.mem_list.tag_configure('rt',   foreground=C_CYAN)
        self.mem_list.tag_configure('user', foreground=C_ORANGE)

    def _refresh_log(self):
        self.log_text.config(state='normal')
        self.log_text.delete(1.0, tk.END)
        for line in self.sim.logs:
            tag = ''
            if '────' in line:      tag = 'tick'
            elif 'de ' in line and ' para ' in line: tag = 'state'
            elif 'RT' in line or 'Tempo Real' in line: tag = 'rt'
            elif 'PREEMPÇÃO' in line or 'Preempção' in line or 'preempt' in line.lower(): tag = 'preempt'
            elif '✓' in line or 'FINALIZADO' in line or 'CONCLUÍDA' in line: tag = 'done'
            elif '⚡' in line or '⚠' in line: tag = 'warn'
            self.log_text.insert(tk.END, line + "\n", tag)
        self.log_text.see(tk.END)
        self.log_text.config(state='disabled')

    # ------------------------------------------------------------------
    # UTILITÁRIOS
    # ------------------------------------------------------------------

    def _panel(self, parent, title):
        """Cria um painel com borda e título estilizado."""
        outer = tk.Frame(parent, bg=C_PANEL,
                         highlightthickness=1, highlightbackground=C_BORDER)
        outer.pack(fill=tk.X, pady=(0, 0))
        tk.Label(outer, text=title, font=C_FONT_HEAD,
                 fg=C_TEXT, bg=C_BORDER, anchor='w',
                 padx=8, pady=3).pack(fill=tk.X)
        inner = tk.Frame(outer, bg=C_PANEL, padx=8, pady=6)
        inner.pack(fill=tk.BOTH, expand=True)
        return inner

    def _btn(self, text, cmd, parent, color):
        tk.Button(parent, text=text, command=cmd,
                  font=C_FONT_BODY, fg=C_BG, bg=color,
                  activebackground=C_TEXT, activeforeground=C_BG,
                  relief='flat', padx=10, pady=4,
                  cursor='hand2').pack(side=tk.LEFT, padx=4, pady=6)

    def _set_status(self, text, color):
        self.lbl_status.config(text=text, fg=color)

    def _is_rt_pid(self, pid):
        """Verifica se um pid pertence a um processo RT."""
        if pid is None:
            return False
        all_procs = (self.sim.unadmitted + self.sim.rt_queue +
                     self.sim.mlfq[0] + self.sim.mlfq[1] + self.sim.mlfq[2] +
                     self.sim.io_wait + self.sim.finished +
                     [p for p in self.sim.cpus if p] +
                     [p for p in self.sim.disks if p])
        for p in all_procs:
            if p.pid == pid:
                return p.ptype == 'RT'
        return False

    def _get_ptype(self, pid):
        if pid is None:
            return 'USER'
        all_procs = (self.sim.unadmitted + self.sim.rt_queue +
                     self.sim.mlfq[0] + self.sim.mlfq[1] + self.sim.mlfq[2] +
                     self.sim.io_wait + self.sim.finished +
                     [p for p in self.sim.cpus if p] +
                     [p for p in self.sim.disks if p])
        for p in all_procs:
            if p.pid == pid:
                return p.ptype
        return 'USER'


# =============================================================================
# GERAÇÃO DO ARQUIVO DE TESTE
# =============================================================================

def create_test_file(path="processos.txt"):
    """Gera o arquivo de teste com os cenários do escopo."""
    lines = [
        "# Formato: [pid, cpu1, io, cpu2, ram_MiB]\n",
        "# Processo 7  — Usuário  (tem I/O, RAM > 512)\n",
        "[7, 4, 2, 4, 800]\n",
        "# Processo 12 — Usuário  (tem I/O, RAM > 512)\n",
        "[12, 10, 4, 8, 1200]\n",
        "# Processo 5  — Tempo Real (sem I/O, sem cpu2, RAM <= 512)\n",
        "[5, 15, 0, 0, 512]\n",
    ]
    with open(path, "w") as f:
        f.writelines(lines)
    return path


# =============================================================================
# ENTRY POINT
# =============================================================================

if __name__ == "__main__":
    # Garante que o arquivo de teste exista ao lado do script
    test_file = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                             "processos.txt")
    if not os.path.exists(test_file):
        create_test_file(test_file)
        print(f"Arquivo de teste criado: {test_file}")

    root = tk.Tk()
    app = AppGUI(root)
    root.mainloop()
