# Eigenraum - 周波数空間における振動エネルギー輸送理論の形式検証

[English](README.md)

振動エネルギーの Density-Driven Dynamics（DDD; 密度駆動動力学）理論とモード空間射影法（MFP）の数学的中核を、Lean 4 と Mathlib で形式化したリポジトリです。

明示した前提から `C = 1 / f` を導く定理列、その帰結として得られる DDD ODE の性質、そして MFP のモード展開と整合する部分を収録します。数値実験やシミュレーションは含みません。

**zero sorry, zero axiom, zero opaque.** Lean `v4.29.0`、Mathlib `v4.29.0`。

## 証明内容

中心となる結論:

- 調和性、弱結合、閉じ込め、紫外有界性、因子化可能性という前提のもとで、モード容量は `C = 1 / f` に定まる。
- MFPの各モードは波動方程式を満たす（順方向）。有限次元では、固有空間の完備性によりモード展開が全解を張る（逆方向）。無限次元の逆方向には追加でコンパクト性（Rellich-Kondrachov）を要する（前提の節を参照）。

そこからさらに:

- DDD ODE で使う構造恒等式
- DDD・SEA的記述・MFPのあいだで不変な観測量
- モード損失則 `γ(f)` から DDD 結合 `k(f)` への一般変換則
- `N_eff = Σ T_α` を中心とした Landauer型チャネル計数
- 非線形補正と空間再構成について、DDD が保持する情報と捨象する情報の切り分け
- LCAMチャネル透過率の基本性質
- MFPのモード展開に必要な定理
- MFPと DDD 輸送の整合性

検証済み公式の一覧と物理的文脈については [FORMULAS-ja.md](./FORMULAS-ja.md)（[English](./FORMULAS.md)）を参照してください。

## 証明の見取り図

### `C = 1 / f` の導出

| ファイル | 内容 |
|---|---|
| `DimensionalAnalysis` | 仕事率の次元を持つべき乗形は `E · ω` に限られる |
| `FluxBasis` | 双線形反対称フラックスは `L` 型と `X` 型に分解できる |
| `Transitivity` | 3モード閉包から `r(r − 1) = 0` を得て、候補が離散化する |
| `UVConvergence` | 紫外発散する枝を有界性で棄却する |
| `Factorization` | `ω_n + ω_m` は `h(ω_n) · h(ω_m)` に因子化できない |
| `MasterTheorem` | 以上をまとめ、因子化可能な弱結合枝で `C = 1 / f` を得る |

### 構造的な結果

| ファイル | 内容 |
|---|---|
| `AlgebraicIdentities` | `k_eff = γ / f`、`k_int = 4πσ₁` などの恒等式 |
| `CouplingTransform` | `γ → k` 変換の加算性、`Q(f)` 変換、`γ ∝ f → k = const` の構造 |
| `NonlinearCapacity` | 非線形容量 `C^NL = 1 / [f(1 + βE)]` とその極限 |
| `NonlinearSpatialExtension` | `ρ_NL = Eω + βωE²` という一次補正と、対角的な空間再構成の構造 |
| `Duality` | `ω ↔ 1/ω` 双対と平衡の対応 |
| `GaugeEquivalence` | `(C, k)` の再パラメータ化不変性 |
| `EquivalenceFramework` | DDD・SEA的記述・action的記述・MFPの間で不変な観測量、MFP-DDD 位相平均一致 |

### LCAM と MFP

| ファイル | 内容 |
|---|---|
| `ChannelTransmission` | `T(s) = 4s(1 − s)` の対称性、上界、最大値 |
| `ChannelCounting` | `N_eff = Σ T_α`、完全混成での飽和、全チャネル平均透過率による分解 |
| `StandingTraveling` | 定在波の重ね合わせから進行波構造が現れること |
| `DampedOscillator` | 減衰振動子の残差消去と関連恒等式 |
| `Completeness` | スペクトル定理の帰結、1D コンパクト性ブリッジ |
| `ModeExpansion` | 変数分離、多モード再構成、有限次元での完備性 |

### 動力学とスペクトル基盤

| ファイル | 内容 |
|---|---|
| `DDDynamics` | 反対称性からの保存則、一意平衡、フラックス方向、Lyapunov代数、指数安定性 |
| `MFPDDDConsistency` | 位相平均したMFPエネルギーが DDD 平衡と整合すること |
| `PhaseAveraging` | 位相平均の形式化: 周期積分、積和公式、クロスモード直交性 |
| `DirichletSpectrum1D` | 1D Dirichlet固有値・直交性・正規化を直接計算で証明 |

## 前提

この導出は以下を仮定する。

| 仮定 | 根拠 |
|---|---|
| 閉じ込めから離散スペクトルが従う | 標準的 (Evans Ch.6)。Mathlib に未実装 |
| ラプラシアンのコンパクト自己共役性 | 同上 (Rellich-Kondrachov) |

位相平均後フラックスの双線形性は `PhaseAveraging.lean` で Fourier 直交性から証明済み。

有限次元 (`eigenspaces_complete_findim`) と 1次元 (`DirichletSpectrum1D`) では上記2項の仮定なしに直接証明している。

## リポジトリ構成

| パス | 役割 |
|---|---|
| `Eigenraum.lean` | ライブラリ全体の入口 |
| `Eigenraum/` | 主題ごとの定理ファイル |
| `lakefile.toml` | Lean パッケージ定義 |
| `lean-toolchain` | Lean バージョン固定 |
| `.github/workflows/` | CI、Mathlib更新ワークフロー |

## ビルド

```bash
lake exe cache get   # ビルド済みMathlibを取得
lake build
```

初回環境では [elan](https://github.com/leanprover/elan) が必要です:

```bash
# macOS
brew install elan-init
```

## 背景記事

- `C = 1/f：モード間エネルギー輸送に関する導出`
  <https://zenn.dev/barineco/articles/395585d1763549>
- `モード空間射影法 (MFP): 空間をリアルタイムで解く波動数値計算`
  <https://zenn.dev/barineco/articles/bcd1776b3a14be>

## コントリビューション

課題報告を歓迎します。[CONTRIBUTING-ja.md](./CONTRIBUTING-ja.md) を参照してください。

## サポート

この成果が役に立った場合は、継続開発を支援できます:

- OFUSE: <https://ofuse.me/barineco>
- Ko-fi: <https://ko-fi.com/barineco>

## ライセンス

Apache License 2.0。[LICENSE](./LICENSE) を参照してください。
