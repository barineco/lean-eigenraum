# 検証済み公式一覧

本文書に掲載するすべての公式は、Lean 4 + Mathlib により形式的に証明されています（`sorry` はゼロ）。
各公式に対応する定理名を併記しています。

用語と記号は [容量 $C = 1/f$ の導出](https://zenn.dev/barineco/articles/395585d1763549)、[MFP の導入](https://zenn.dev/barineco/articles/bcd1776b3a14be)、および執筆中の結合定数カタログ・LCAM 混成モードの記事に準拠しています。

---

## 略語

| 略語 | 正式名称 | 意味 |
|------|---------|------|
| DDD | Density-Driven Dynamics（密度駆動動力学） | 音響密度の差 $\Delta\rho$ を駆動力とするモード間エネルギー輸送の記述 |
| MFP | Modal Field Projection（モード空間射影法） | 空間場をモード基底に展開し、各モードを減衰振動子として解析的に時間発展させ、空間場を再合成する手法 |
| LCAM | Linear Combination of Acoustic Modes（音響モードの線形結合） | 量子化学の LCAO（原子軌道の線形結合）と同じ行列構造を音響モードに適用し、結合系の混成モードを構成する枠組み |
| SEA | Statistical Energy Analysis（統計的エネルギー解析） | モード間のエネルギー等分配を仮定する伝統的手法。 $r = 1$ の記述に対応する |

---

## $f$ と $\omega$ の対応

音響や構造振動の文脈では、容量は $C = 1/f$（$f$ [Hz]）と書くのが自然です。記事群もこの表記を採用しています。一方、本形式化では三角関数や微分方程式との整合のため、角振動数 $\omega = 2\pi f$ [rad/s] を基本変数としています。

両者の関係は次の通りです。

$$
C = \frac{1}{f} = \frac{2\pi}{\omega}
$$

$2\pi$ の因子は容量に残すことも結合定数に移すこともでき、観測量（フラックス $J = k\Delta\rho$）は変わりません。具体的には:

| 表記 | 容量 | 密度 | 結合定数 |
|------|------|------|----------|
| $f$ 表記（記事） | $C = 1/f$ | $\rho = Ef$ | $k_f$ |
| $\omega$ 表記（本形式化） | $C = 1/\omega$ | $\rho = E\omega$ | $k_\omega = k_f / (2\pi)$ |

フラックスは $k_f \cdot E f = k_\omega \cdot E\omega$ で一致します。本形式化では $\omega$ 表記を採り、 $k$ は $k_\omega$ の意味で使っています。記事群の数値と比較する際は $2\pi$ の位置に注意してください。

---

## 記号一覧

| 記号 | 物理量 | 単位・備考 |
|------|--------|------------|
| $E_n$ | モード $n$ のエネルギー | J |
| $\omega_n$, $f_n$ | モード $n$ の角振動数・周波数 | rad/s, Hz。 $\omega = 2\pi f$ |
| $C_n$ | モード容量。エネルギーを音響密度に変換する係数 | $C_n = E_n / \rho_n$ |
| $\rho_n$ | モード $n$ の音響密度。DDD 方程式の駆動変数 | $\rho_n = E_n \omega_n$（$\omega$ 表記）。上節参照 |
| $T$ | 全モード共通の平衡密度 $\rho_n^{\mathrm{eq}} = T$ | |
| $k$ | DDD 結合定数。モード間のエネルギーの流れやすさ | 1/s。弱結合でモード対に依存しないスカラー |
| $K_{nm}$ | 結合テンソル。 $k$ はその対称的縮約 | |
| $\gamma_n$ | モード $n$ の減衰率（振幅の指数減衰定数） | rad/s |
| $\sigma_0$ | 速度比例損失係数。 $\gamma = 2\sigma_0$（周波数非依存） | 1/s。空気抵抗など外部摩擦に対応 |
| $\sigma_1$ | Kelvin–Voigt 粘性係数。 $\gamma = 4\pi\sigma_1 f$（周波数比例） | s。材料内部損失に対応 |
| $Q$ | 品質係数。 $Q = \pi f / \gamma$ | 無次元 |
| $\beta$ | 非線形補正パラメータ。Duffing 振動子的な周波数のエネルギー依存性 | 1/J |
| $r$ | フラックス基底の混合比 $r = \beta_X / \beta_L$ | 無次元。 $r = 0$: DDD、 $r = 1$: SEA |
| $s_\alpha$ | 混成モード $\alpha$ の部分系 A への帰属度 | 無次元。 $\sum_{n \in A} \|c_{\alpha n}\|^2$。弦-響板系では弦性 |
| $T_\alpha$ | チャネル $\alpha$ の透過率 | 無次元。 $T_\alpha = 4s_\alpha(1 - s_\alpha)$ |
| $N_{\mathrm{eff}}$ | 有効チャネル数（Landauer 型） | 無次元。 $\sum_\alpha T_\alpha$ |
| $c$ | 波動伝搬速度 | m/s |
| $L$ | 領域の長さ（1D Dirichlet 問題） | m |
| $k_n$ | 空間波数 $k_n = n\pi/L$ | rad/m |
| $\psi_n(x)$ | 空間固有関数（サイトモード）。 $\sin(k_n x)$ | |
| $q_n(t)$ | 時間モード振幅。減衰振動子 $e^{-\gamma t}\sin(\omega t)$ の解 | |

---

## 前提 [P1]–[P4b]

容量の導出で用いる前提条件。ラベルは記事1に準拠。

| ラベル | 名称 | 内容 |
|--------|------|------|
| [P1] | 調和性 | 振動数 $\omega_n$ はエネルギー $E_n$ に依存しない |
| [P2] | 弱結合性・双線形性 | 結合はモードの振動数を変えない。フラックスは各モードのエネルギーについて1次 |
| [P3] | 閉じ込め | 有限領域の境界条件が離散スペクトルを生む |
| [P4a] | 因子化可能性 | $k_{nm} = h(\omega_n) \cdot h(\omega_m)$ の形に分離可能 |
| [P4b] | 高周波エネルギー収束 | $E_n$ が $\omega_n \to \infty$ で発散しない |

[P1]–[P3] がフラックスの候補を3つの離散解 ($r \in \{0, 1, \infty\}$) に限定し、[P4b] が紫外発散する $r = \infty$ を棄却し、[P4a] が $r = 1$ を排除して $r = 0$（$C = 1/f$）を選択する。

---

## 容量と密度

前提: [P1]–[P3], [P4a], [P4b]

マスター容量選択則（`MasterTheorem.master_capacity_selection`）：

$$
C_n = \frac{1}{\omega_n}
$$

各モードのエネルギーを音響密度に変換する係数。高い周波数ほど容量が小さく、同じエネルギーでも密度が高い。

音響密度の定義：

$$
\rho_n = E_n \omega_n
$$

DDD 方程式の基本変数。平衡で全モード一定値 $T$ をとる。「密度」の名称は、エネルギーの充填度合いを表す量であることに由来する。

非線形零フラックス条件（`NonlinearCapacity.zero_flux_NL`）：

$$
\rho_n^{\mathrm{NL}} = E_n \omega_n (1 + \beta E_n)
$$

振動振幅に依存する補正を含む非線形密度。[P1]（調和性）を緩和した場合に現れる。 $\beta \to 0$ で線形理論に帰着する。

非線形密度の線形＋二次分解（`NonlinearSpatialExtension.rho_nl_linear_plus_quadratic`）：

$$
\rho_n^{\mathrm{NL}} = E_n \omega_n + \beta \omega_n E_n^2
$$

非線形密度を線形部分（DDD が追跡する情報）と二次補正（DDD が捨象する情報）に分離する。

---

## DDD ODE（密度駆動 ODE）

前提なし。以下はすべて $k > 0$, $\omega_n > 0$ のもとでの代数的帰結です。

2 モード DDD ダイナミクス（`DDDynamics`）：

$$
\frac{dE_1}{dt} = -k(\rho_1 - \rho_2), \quad \frac{dE_2}{dt} = +k(\rho_1 - \rho_2)
$$

音響密度の差 $\Delta\rho$ に比例してエネルギーが流れる。密度の高いモードから低いモードへの一方向輸送。

エネルギー保存則（`DDDynamics.energy_conservation`）：

$$
\frac{dE_1}{dt} + \frac{dE_2}{dt} = 0
$$

散逸のない系での全エネルギーの保存。

N モードエネルギー保存則（`DDDynamics.energy_conservation_n`）：

$$
\sum_i \sum_j J(i,j) = 0 \quad \text{（前提: } J(i,j) = -J(j,i) \text{）}
$$

任意の $N$ モード系でペアワイズ反対称なフラックスの総和がゼロ。 $S = -S$ から $S = 0$ を導く。

平衡分布（`DDDynamics.equilibrium_distribution`）：

$$
E_n^{\mathrm{eq}} = \frac{T}{\omega_n}
$$

音響密度均等化 $\rho_n = T$ における各モードのエネルギー。高周波モードほど平衡エネルギーが小さい。

Lyapunov 関数の代数構造（`DDDynamics.lyapunov_algebraic`）：

$$
\frac{d(\Delta\rho)^2}{dt} = -2k(\omega_1 + \omega_2)(\Delta\rho)^2
$$

密度差の二乗の時間微分が常に非正であることの代数的導出。

平衡の特徴づけ（`DDDynamics.lyapunov_zero_iff_equilibrium`）：

$$
\frac{d(\Delta\rho)^2}{dt} = 0 \iff \Delta\rho = 0
$$

Lyapunov 微分がゼロになるのは平衡のときに限る。

安定性バウンド（`DDDynamics.exponential_decay_bounded`）：

$$
|\Delta\rho_0 \cdot e^{-\lambda t}| \le |\Delta\rho_0| \quad (t \ge 0,\; \lambda > 0)
$$

$\lambda = k(\omega_1 + \omega_2)$ は系の緩和レート。密度差が初期偏差を超えないことの保証。

漸近安定性（`DDDynamics.density_difference_decays`）：

$$
\Delta\rho_0 \cdot e^{-\lambda t} \to 0 \quad (t \to \infty,\; \lambda > 0)
$$

密度差は指数的にゼロに収束する。`Filter.Tendsto` による証明。

---

## 結合変換

前提なし。 $f \neq 0$ のもとでの代数的恒等式です。

減衰率 $\gamma$（モード空間の損失定数）を DDD 結合定数 $k$（密度空間の輸送レート）に変換する公式群。 $k = \gamma/f$ は $\rho = Ef$ の定義から従う代数的恒等式であり、この変換を既知の損失モデルに適用すると密度空間における $k$ の周波数構造が現れる。

有効結合定数（`AlgebraicIdentities.k_eff_identity`）：

$$
k_{\mathrm{eff}} = \frac{\gamma}{f}
$$

$C = 1/f$ が $\gamma$ と $k$ の間に構造的な $1/f$ 因子を生む。 $\gamma E = k\rho$ の関係。

べき乗則の定数結合条件（`CouplingTransform.powerlaw_constant_iff_alpha_eq_one`）：

$$
k = \text{const} \iff \alpha = 1
$$

$\gamma \propto \omega^\alpha$ のとき $k \propto \omega^{\alpha - 1}$。 $\alpha = 1$（周波数比例損失）でのみ $k$ が周波数に依存しない。

Kelvin–Voigt 内部損失による定数結合（`CouplingTransform.kelvin_voigt_gives_constant_k`）：

$$
k_{\mathrm{int}} = 4\pi\sigma_1
$$

$\gamma = 4\pi\sigma_1 f$（$\alpha = 1$）のとき、 $k$ は周波数によらない定数。材料内部の粘性損失に対応する。

Q 値からの結合定数（`CouplingTransform.k_of_quality_factor`）：

$$
k = \frac{\pi}{Q}
$$

$\gamma = \pi f / Q$ から得られる。 $Q$ が大きい（損失が小さい）ほど $k$ は小さい。

結合変換の加法性（`CouplingTransform.k_of_gamma_additive`）：

$$
k(\gamma_1 + \gamma_2) = k(\gamma_1) + k(\gamma_2)
$$

独立な損失メカニズムは密度空間でも加算的に合成される。

---

## LCAM チャネル透過

前提なし。 $s_\alpha \in [0, 1]$ のもとでの解析です。

LCAM（Linear Combination of Acoustic Modes）は、離散モードを持つ二つの部分系（例: 弦と響板）が結合するとき、部分系のサイトモード $\phi_j$ の線形結合として混成モード $\Phi_\alpha = \sum_j c_{\alpha j} \phi_j$ を構成する。結合行列 $H$ の固有値問題に帰着し、LCAO と同一の数学的骨格を持つ。

$s_\alpha = \sum_{n \in A} |c_{\alpha n}|^2$ は、混成モード $\alpha$ のエネルギーのうち部分系 A のサイトモードに由来する割合を表す。弦-響板系では弦性（ストリング性）と呼ばれる。

LCAM 透過率（`ChannelTransmission.T_lcam`）：

$$
T_\alpha = 4\, s_\alpha (1 - s_\alpha), \quad s_\alpha \in [0, 1]
$$

混成モード $\alpha$ を通じたエネルギー透過率。純サイトモード ($s = 0$ or $1$) では $T = 0$、完全混成 ($s = 1/2$) で $T = 1$。

透過率の対称性（`ChannelTransmission.T_symmetric`）：

$$
T(s) = T(1 - s)
$$

部分系 A と B の寄与を入れ替えても透過率は不変。弦-響板系なら $s$ と $1-s$ の交換に対応する。

最大透過の一意性（`ChannelTransmission.T_max_unique`）：

$$
T = 1 \iff s = \frac{1}{2}
$$

完全透過を達成するのは二つの部分系が等しく寄与する混成モードに限られる。

有効チャネル数の上界（`ChannelCounting.neff_le_raw_count`）：

$$
N_{\mathrm{eff}} = \sum_\alpha T_\alpha \le N
$$

有効チャネル数は幾何学的チャネル数 $N$ を超えない。Landauer 型チャネル計数。

有効チャネル数の因子分解（`ChannelCounting.neff_factorization_full`）：

$$
N_{\mathrm{eff}} = N \cdot \langle T \rangle
$$

有効チャネル数 = チャネル数 $\times$ 平均透過率。全モードが $s = 1/2$ なら $N_{\mathrm{eff}} = N$。

---

## ゲージ同値性

前提なし。純粋な代数的恒等式です。

単一経路のフラックスは $(C, k)$ の選び方を変えても同じ観測値を生む。 $C = 1/f$ の選択はデータフィッティングではなく、[P1]–[P4] によってのみ決まる。

フラックスの代数的分解（`GaugeEquivalence.flux_algebraic_decomposition`）：

$$
E_n\omega_n - E_m\omega_m = \frac{\omega_n + \omega_m}{2}(E_n - E_m) + \frac{E_n + E_m}{2}(\omega_n - \omega_m)
$$

DDD フラックス（左辺）を SEA 的なエネルギー差の項と周波数差の項に分解する。等周波数で後者が消える。

容量–結合トレードオフ（`GaugeEquivalence.capacity_k_tradeoff`）：

$$
(\alpha + \Delta\alpha) + (\beta - \Delta\alpha) = \alpha + \beta
$$

容量のべき指数をシフトすると結合のべき指数が逆方向にシフトし、観測量（総指数）は不変。

---

## 双対性

前提なし。周波数パラメータ上の代数的対称性です。

周波数反転による交換（`Duality.L_becomes_X_under_inversion`）：

$$
\omega \leftrightarrow \frac{1}{\omega} \quad \text{は} \quad r = 0 \;\text{と}\; r = \infty \;\text{を交換する}
$$

$r = 0$（DDD）の平衡 $E\omega = T$ と $r = \infty$ の平衡 $E/\omega = T$ は周波数反転で入れ替わる。

自己双対点（`Duality.r1_self_dual`）：

$$
r = 1 \;\text{は自己双対}
$$

$r = 1$（SEA）の平衡 $E = T$ は $\omega \leftrightarrow 1/\omega$ で不変。

---

## 位相平均

前提なし。三角関数の積分恒等式です。

MFP は位相（$e^{-\gamma t}\sin\omega t$ の振動構造）を保持するが、DDD はエネルギー（位相平均後の量）のみを追跡する。以下の積分公式がその橋渡しを支える。

正弦二乗の周期積分（`PhaseAveraging.integral_sin_sq_period`）：

$$
\int_0^{2\pi} \sin^2\theta\, d\theta = \pi
$$

正弦・余弦の直交性（`PhaseAveraging.integral_sin_mul_cos_period`）：

$$
\int_0^{2\pi} \sin\theta \cos\theta\, d\theta = 0
$$

位相平均エネルギー（`PhaseAveraging.phase_averaged_energy`）：

$$
\frac{1}{2\pi}\int_0^{2\pi}\!\bigl[(\gamma^2 + \omega^2)\sin^2\theta - 2\gamma\omega\sin\theta\cos\theta + \omega^2\cos^2\theta\bigr]\,d\theta = \omega^2 + \frac{\gamma^2}{2}
$$

MFP エネルギー被積分関数を 1 周期で平均すると DDD が追跡するエネルギーに一致する。振動成分は平均で消える。

交差モード分解（`PhaseAveraging.cross_mode_decomposition`）：

$$
\sin(\omega_n t)\sin(\omega_m t) = \frac{1}{2}\bigl[\cos((\omega_n - \omega_m)t) - \cos((\omega_n + \omega_m)t)\bigr]
$$

異なるモードの積を和差周波数に分解する。ビート周期での時間平均がゼロになることの基礎。

---

## MFP モード展開

前提なし。三角関数の恒等式と、 $c \neq 0$, $L \neq 0$ のもとでの代数です。

MFP は波動場を $G(x,t) = \sum_n q_n(t)\psi_n(x)$ とモード展開し、各 $q_n(t)$ を減衰振動子として解析的に時間発展させる。定在波の重ね合わせから波面伝搬が現れることが MFP の着想の起源である。

定在波の進行波分解（`StandingTraveling.standing_wave_decomposition`）：

$$
\cos(kx)\cos(\omega t) = \frac{1}{2}\bigl[\cos(kx - \omega t) + \cos(kx + \omega t)\bigr]
$$

定在波は左右の進行波の重ね合わせ。定在波の和が巨視的な波面伝搬を生む起源。

ビート周期と往復時間（`StandingTraveling.beat_period_eq_round_trip`）：

$$
T_{\mathrm{beat}} = \frac{2L}{c}
$$

隣接モードのビート周期は波の往復時間に等しい。MFP の時間分解能の下限を与える。

パケット幅（`StandingTraveling.packet_width`）：

$$
\Delta x = \frac{2L}{N}
$$

$N$ モードの重ね合わせで再構成できる空間分解能。

PDE 残差消滅（`ModeExpansion.pde_residual_vanishes`）：

固有関数性 $L\psi = \lambda\psi$ と時間 ODE の成立のもとで、 $q(t)\psi(x)$ の PDE 残差がゼロ。モード展開の各項が波動方程式を満たすことの代数的証明。

分散関係式（`ModeExpansion.dispersion_sq`）：

$$
\omega^2 = c^2 k^2
$$

空間波数 $k$ と角振動数 $\omega$ の関係。閉じ込め条件 $k_n = n\pi/L$ と合わせて離散スペクトルを与える。

有限次元での固有空間完備性（`ModeExpansion.findim_eigenspaces_span_all`）：

有限次元の自己共役作用素に対し、コンパクト性の仮定なしで固有空間が全空間を張る。PDE 残差消滅と合わせると、有限次元ではモード展開と波動方程式の同値性が成立する。

---

## 1次元 Dirichlet スペクトル

前提なし。 $L > 0$, $n > 0$ のもとでの固有値理論です。

$[0, L]$ 上の Dirichlet 境界条件（両端固定）における固有モードの明示的計算。Rellich–Kondrachov 不要。

固有値（`DirichletSpectrum1D.dirichlet_ev`）：

$$
\lambda_n = \left(\frac{n\pi}{L}\right)^2
$$

$n$ 番目の固有値。 $\omega_n^2 = c^2\lambda_n$ で角振動数を与える。

直交性（$n \ne m$）（`DirichletSpectrum1D.dirichlet_orthogonality`）：

$$
\int_0^L \sin\!\left(\frac{n\pi x}{L}\right)\sin\!\left(\frac{m\pi x}{L}\right)\,dx = 0
$$

異なるモードの内積がゼロ。モード展開係数を独立に求められる根拠。

正規化（`DirichletSpectrum1D.dirichlet_normalization`）：

$$
\int_0^L \sin^2\!\left(\frac{n\pi x}{L}\right)\,dx = \frac{L}{2}
$$

各固有関数のノルム。 $\sqrt{2/L}\,\sin(n\pi x/L)$ が正規直交基底となる。

固有値ギャップ（`DirichletSpectrum1D.dirichlet_ev_gap`）：

$$
\lambda_{n+1} - \lambda_n = (2n + 1)\left(\frac{\pi}{L}\right)^2
$$

隣接固有値の差は $n$ に線形に増大する。高周波ほどモード間隔が広い。

---

## MFP-DDD 整合性

位相平均した MFP エネルギーが DDD エネルギーと一致する（`EquivalenceFramework.ddd_mfp_phase_average_agreement`）：

$$
\frac{1}{2\pi}\!\left[(\gamma^2 + \omega^2)\!\int_0^{2\pi}\!\sin^2\theta\,d\theta - 2\gamma\omega\!\int_0^{2\pi}\!\sin\theta\cos\theta\,d\theta + \omega^2\!\int_0^{2\pi}\!\cos^2\theta\,d\theta\right] = \omega^2 + \frac{\gamma^2}{2}
$$

MFP が追跡する位相つきのエネルギーを 1 周期で平均すると DDD が追跡するエネルギーに一致する。PhaseAveraging の周期積分結果（$\int\sin^2 = \pi$, $\int\cos^2 = \pi$, $\int\sin\cos = 0$）を代入して証明。MFP と DDD の橋渡し。

---

## スペクトル定理

前提: コンパクト自己共役作用素 $T$。

コンパクト自己共役作用素の固有空間は $H$ を張る（`Completeness.eigenspaces_complete`）。

モード展開が完全であることの関数解析的保証。任意の $v \in H$ を固有ベクトルの線形結合で表せる。

有限次元の場合、コンパクト性は不要（`Completeness.eigenspaces_complete_findim`）。

有限次元の自己共役行列は常に対角化可能であるという線形代数の基本定理に相当。

固有空間は互いに直交する（`Completeness.eigenspaces_orthogonal`）。

異なる固有値に属する固有ベクトルの内積がゼロ。モード間のエネルギー独立性の数学的基盤。

固有値は実数である（`Completeness.eigenvalues_conjugate_invariant`）。

振動数の二乗 $\omega_n^2$ が実数であることの保証。

### 1D コンパクト性ブリッジ

1D スペクトルパッケージ（`Completeness.compact_self_adjoint_spectral_package`）：

コンパクト自己共役作用素に対し、固有空間の完備性と非零固有空間の有限次元性を一つの定理にパッケージ化。1D では Arzelà–Ascoli から `IsCompactOperator` が得られるため（Rellich–Kondrachov 不要）、このパッケージがそのまま適用できる。

1D Dirichlet スペクトルブリッジ（`Completeness.dirichlet_spectral_bridge`）：

$$
c^2 \cdot \left(\frac{n\pi}{L}\right)^2 = \left(\frac{n\pi c}{L}\right)^2 \quad \text{かつ} \quad \left(\frac{n\pi}{L}\right)^2 > 0
$$

分散関係と固有値の正値性を一つの定理にまとめる。抽象側（`eigenspaces_complete`: コンパクト自己共役作用素のスペクトル定理）と具体側（`dirichlet_dispersion`: 1D Dirichlet 固有値の明示公式）の接続点。
