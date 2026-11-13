# 平坦性传递的局部倾斜、应力估计与指数尾部

本章从已有的球质量等式推出局部倾斜趋零，直接在单相能量中证明 Caccioppoli 估计，仅用二阶势能正则性证明正平衡点附近的指数尾部，并计算归一化法向通量的边缘误差。这些局部估计由后续调和近似和方向迭代章节组合成完整的倾斜改进。

## FE1. 从原点球上的精确质量得到任意紧集上的倾斜趋零

设环境维数为 n，界面维数为 m，其中 m 等于 n 减一。设 e 为单位向量，放大后的解和原函数记为

$$
v_j(x)=\bar u(R_jx),\qquad
p_j(x)=\Phi(v_j(x)),\qquad
\Phi(s)=\int_0^s\sqrt{2W(a)}\,da,\qquad \sigma=\Phi(1).
$$

假定尺度趋于无穷，并且同一个放大序列满足

$$
v_j\longrightarrow\mathbf1_H\quad\text{于 }L^1_{\mathrm{loc}},
\qquad H=\{x:x\cdot e>0\},
$$

$$
\lim_{j\to\infty}\int_{B_r}|\nabla p_j|\,dx
=\sigma\omega_m r^m\qquad(r>0).
\tag{FE1.1}
$$

这里原点球的质量等式来自已证明的 `PrimitivePerimeterMass.lean`，再计算半空间在球内的周长。假定零延拓局部 Lipschitz、取值在闭单位区间，且正相内满足缩放后的 Modica 界

$$\tfrac12R_j^{-2}|\nabla v_j|^2\le W(v_j).$$

原函数同样局部 Lipschitz，链式法则按几乎处处的梯度解释。球的开闭差别是球面零体积，不影响这些积分。

**结论。** 对任意紧集 K，

$$
\lim_{j\to\infty}\int_K R_j^{-1}
\left(|\nabla v_j|^2-(e\cdot\nabla v_j)^2\right)dx=0.
\tag{FE1.2}
$$

**证明。** 原函数在闭单位区间的导数有界，故为 Lipschitz 函数。将相位的局部积分收敛代入其 Lipschitz 界，得到

$$
p_j\longrightarrow\sigma\mathbf1_H\quad\text{于 }L^1_{\mathrm{loc}}.
$$

对任意紧支撑连续可微测试函数 eta，分部积分给出

$$
\int\eta\,e\cdot\nabla p_j
=-\int p_j\,e\cdot\nabla\eta
\longrightarrow-\sigma\int_H e\cdot\nabla\eta.
$$

选择正交坐标，使最后坐标方向为 e。固定其余坐标，对正半直线积分 eta 的最后偏导数，积分基本定理给出负的 eta 在零截面的值；无穷端值为零，因为 eta 紧支撑。再用 Fubini，得

$$
-\sigma\int_H e\cdot\nabla\eta
=\sigma\int_{e^\perp}\eta\,d\mathcal H^m.
\tag{FE1.3}
$$

任取正数 r、s，且 r 小于 s。取光滑截断 eta，在 r 球上等于 1，支撑包含于 s 球，且值介于 0 和 1 之间。由单位向量 Cauchy–Schwarz 不等式，

$$
d_j:=|\nabla p_j|-e\cdot\nabla p_j\ge0.
$$

所以

$$
\begin{aligned}
0\le\int_{B_r}d_j
&\le\int\eta d_j\\
&\le\int_{B_s}|\nabla p_j|-\int\eta e\cdot\nabla p_j.
\end{aligned}
$$

使用 FE1.1 和 FE1.3，并注意 eta 在平面与 r 球的交集中等于 1，得到

$$
0\le\limsup_j\int_{B_r}d_j
\le\sigma\omega_m(s^m-r^m).
$$

此不等式对每个大于 r 的 s 成立。让 s 下降到 r，右侧趋零，故 r 球上缺陷积分趋零。

在正相内令

$$
a_j=R_j^{-1/2}|\nabla v_j|,\qquad
b_j=\sqrt{2R_jW(v_j)}.
$$

Modica 估计给出 a 不超过 b，而链式法则给出

$$
|\nabla p_j|=a_jb_j.
$$

在梯度非零处记其单位方向为 nu，并令 c 为该方向与 e 的内积。因为 c 在负一到一之间，

$$
1-c^2=(1-c)(1+c)\le2(1-c).
$$

从而

$$
R_j^{-1}\left(|\nabla v_j|^2-(e\cdot\nabla v_j)^2\right)
=a_j^2(1-c^2)
\le2a_jb_j(1-c)=2d_j.
$$

梯度为零时两侧皆零。在零相内，局部 Lipschitz 非负函数的梯度几乎处处为零，故同一不等式仍成立。把任意紧集包含在某个原点球中，以非负性比较积分，结论随之成立。

此证明不需要先构造 varifold，也不需要先证明任意中心球的精确能量极限；已有的原点球质量等式就足够。

## FE2. 带明确边缘误差的单相 Caccioppoli 不等式

写坐标为水平变量 y 与最后变量 t。设 epsilon 为正，v 为连续、局部 Lipschitz、非负的单相函数。定义几乎处处的能量密度与非负差额

$$
e_\varepsilon=
\frac\varepsilon2|\nabla v|^2+
\frac1\varepsilon W(v)\mathbf1_{\{v>0\}},
\qquad
D_\varepsilon=
\frac1\varepsilon W(v)\mathbf1_{\{v>0\}}
-\frac\varepsilon2|\nabla v|^2\ge0.
$$

假定对每个紧支撑连续可微向量场 X，有整个空间上的应力驻定等式

$$
\int\left(e_\varepsilon\operatorname{div}X
-\varepsilon\langle DX\nabla v,\nabla v\rangle\right)=0.
\tag{FE2.1}
$$

这正是单相问题应当使用的驻定性，已经包括自由边界条件。当前项目的 `StressStationarity.lean` 已证明原解的这一性质；缩放给出此形式。

设 phi 是水平空间上的紧支撑连续可微函数，psi 是最后坐标上的紧支撑连续可微函数，lambda 为任意实常数。则

$$
\begin{aligned}
\int\phi^2\psi^2\varepsilon|\nabla_yv|^2
&\le4\int\psi^2(t-\lambda)^2\varepsilon v_t^2|\nabla\phi|^2\\
&\quad+4\int\phi^2|\psi\psi'(t-\lambda)|e_\varepsilon.
\end{aligned}
\tag{FE2.2}
$$

事实上，左侧可以替换成更大的积分，其被积项为

$$
\phi^2\psi^2 A_\varepsilon,
\qquad A_\varepsilon=e_\varepsilon-\varepsilon v_t^2
=\varepsilon|\nabla_yv|^2+D_\varepsilon.
$$

**证明。** 以

$$
X(y,t)=\phi(y)^2\psi(t)^2(t-\lambda)e_n
$$

为 FE2.1 的测试向量场。其散度为

$$
\phi^2\psi^2+2\phi^2\psi\psi'(t-\lambda).
$$

其导数作用在两个梯度上所得二次项为

$$
v_t^2\left(\phi^2\psi^2+2\phi^2\psi\psi'(t-\lambda)\right)
+2\phi\psi^2(t-\lambda)v_t\nabla_yv\cdot\nabla\phi.
$$

代入并移动项，得到精确恒等式

$$
\begin{aligned}
I:=\int\phi^2\psi^2A_\varepsilon
&=2\int\phi\psi^2(t-\lambda)\varepsilon v_t
\nabla_yv\cdot\nabla\phi\\
&\quad-2\int\phi^2\psi\psi'(t-\lambda)A_\varepsilon.
\end{aligned}
$$

由差额非负，A 非负且至少为 epsilon 乘水平梯度平方；由其定义，A 不超过能量密度。第一项逐点应用

$$
2ab\le\tfrac12a^2+2b^2
$$

其中 a 取 phi、psi 的绝对值乘 epsilon 平方根和水平梯度长度，b 取 psi、t 减 lambda 的绝对值乘 epsilon 平方根、最后偏导数绝对值和 phi 梯度长度。于是第一项至多为 I 的一半，加上 FE2.2 第一项的一半。第二项取绝对值并使用 A 不超过能量，得到 FE2.2 第二项的一半。移走 I 的一半，再乘 2，得所述更强不等式，继而得到 FE2.2。

这个证明只使用驻定性、Modica 符号和一阶测试函数。没有求势能三阶导数，也没有把正相内的分部积分误当作全空间公式。若从 PDE 而非已证明的驻定性开始，则自由边界应力为零是必须补齐的前置步骤。

## FE3. 二阶势能即可给出的指数尾部

设 W 在闭单位区间二次连续可微，在 1 处函数值和一阶导数均为零。取零与一之间的 b 及正数 c、C，使在闭区间从 1 减 b 到 1 上有

$$
c\le W''\le C.
$$

设正相解 v 在下面开立方体的闭包的一个邻域内二次连续可微：

$$
Q_L=\{x:|x_i|<L,\ i=1,\ldots,n\}
$$

并满足

$$
\varepsilon^2\Delta v=W'(v),\qquad 1-b\le v\le1.
$$

令 w 为 1 减 v。积分 W 的二阶导数界，得到

$$
cw\le-W'(v)\le Cw,
\qquad \tfrac c2w^2\le W(v)\le\tfrac C2w^2.
$$

因此

$$
\Delta w\ge\frac c{\varepsilon^2}w.
$$

设 k 等于 c 的平方根除以 epsilon，定义显式屏障

$$
B(x)=b\sum_{i=1}^n\frac{\cosh(kx_i)}{\cosh(kL)}.
$$

直接二次求导得

$$
(\Delta-k^2)B=0.
$$

在立方体边界至少一个坐标绝对值为 L，因此 B 至少为 b，进而至少为 w。若 w 减 B 在内部有严格正的最大值，那里 Laplacian 非正，所以算子 Delta 减 k 平方作用于该差严格为负；但由 w 的不等式和 B 的等式，这个算子值非负，矛盾。故 w 不超过 B。

任取正 d 小于 L。在较小立方体上，利用双曲余弦的指数定义，

$$
\frac{\cosh(kx_i)}{\cosh(kL)}
\le2e^{-kd}\qquad(|x_i|\le L-d).
$$

因此得到完整定量界

$$
0\le1-v(x)\le2nb\exp\left(-\frac{\sqrt c\,d}{\varepsilon}\right)
\qquad(x\in Q_{L-d}).
\tag{FE3.1}
$$

若同时满足 Modica 不等式，则

$$
\varepsilon|\nabla v|\le\sqrt{2W(v)}\le\sqrt C\,(1-v),
$$

$$
e_\varepsilon\le\frac{2W(v)}\varepsilon
\le\frac{4Cn^2b^2}{\varepsilon}
\exp\left(-\frac{2\sqrt c\,d}{\varepsilon}\right)
\qquad(x\in Q_{L-d}).
\tag{FE3.2}
$$

注意 FE3 的前提是在整个较大立方体上已进入正平衡点邻域。仅有局部积分趋向 1，不足以直接使用这个前提；从积分收敛推出整个区域进入该邻域仍需要清除小能量区域中的过渡层的定量结果。零相一侧若已证明函数恒零，则能量直接为零，不需要给零相套用 FE3。

## FE4. 调和近似之前的水平通量恒等式与误差尺度

在 FE2 的相同前提下，以另外一个向量场

$$
X(y,t)=\varphi(y)\psi(t)e_n
$$

测试整个空间的应力等式。其散度是 varphi 乘 psi 的导数；对应二次项是

$$
v_t\psi\,\nabla_yv\cdot\nabla\varphi
+v_t^2\varphi\psi'.
$$

逐项代入给出精确的通量恒等式

$$
\int\varepsilon\psi v_t\nabla_yv\cdot\nabla\varphi
=\int\varphi\psi' A_\varepsilon.
\tag{FE4.1}
$$

因此

$$
\left|\int\varepsilon\psi v_t\nabla_yv\cdot\nabla\varphi\right|
\le\|\varphi\|_\infty\int_{\operatorname{supp}\varphi\times
\operatorname{supp}\psi'}|\psi'|e_\varepsilon.
\tag{FE4.2}
$$

假定右侧支撑落在两个固定区域中：一个区域内解恒零；另一个区域被有限个 FE3 的较小立方体覆盖，且这些较小立方体到各自较大立方体边界的距离至少为固定正数 d。假定相关势能凸性常数、截断函数、覆盖立方体数和体积都与 epsilon 无关。FE3.2 及有限求和就给出

$$
\left|\int\varepsilon\psi v_t\nabla_yv\cdot\nabla\varphi\right|
\le C_0\varepsilon^{-1}e^{-a/\varepsilon}
\tag{FE4.3}
$$

其中 a 可取为两倍 c 平方根乘 d，C0 由覆盖体积和截断界明确组成。FE2 中含 psi 导数的边缘误差在相同条件下具有同一形式的上界，额外乘上固定支撑上 t 减 lambda 的上界。

若归一化倾斜幅度 delta 满足

$$
\delta_\varepsilon\ge K\varepsilon,\qquad K>0,
$$

那么 FE4.3 除以 delta 或其平方仍趋零。以平方为例，

$$
0\le\frac{C_0\varepsilon^{-1}e^{-a/\varepsilon}}
{\delta_\varepsilon^2}
\le\frac{C_0}{K^2}\varepsilon^{-3}e^{-a/\varepsilon}
\longrightarrow0.
$$

最后一个极限可直接证明：令 z 为 a 除 epsilon。指数函数的幂级数给出指数 z 至少为 z 的四次方除 24，所以 z 的三次方乘负 z 的指数至多为 24 除 z，趋于零。其它固定幂次同理。

这补齐了调和近似中截断顶底面的误差除以倾斜后消失的量化计算。FE4.1 左侧仍是原解的通量；把它变为归一化高度函数梯度积分所需的层面坐标公式、权重收敛及坏集误差，分别在 [HA2、HA4、HA9–HA11](harmonic-approximation.md) 中证明。

## FE5. 二阶势能的正则性核对与后续衔接

FE1 不对势能求导，只用连续的平方根、链式法则、Modica 和已有质量等式。FE2 完全不对势能求导。FE3 只用 W 的二阶导数上下界，而且常数已经明确：不会依赖三阶导数。

倾斜改进的源论文 [Wang, §2、§4、§7–8](https://arxiv.org/pdf/1401.6480) 在整体设置中使用三阶势能正则性。这里对实际使用的估计逐项重证，不声称修改了该文全部结果的假设。[HA5](harmonic-approximation.md) 对导数的弱方程使用连续的势能二阶导数，展开 Bochner 测试时不再求导该系数；[HA9–HA10](harmonic-approximation.md) 对零端点只使用连续剖面与清除。

尤其不能简单取光滑势能逼近，再把原解代入光滑势能定理：原解不满足改变后的 PDE。若另构造近似极小解，则还必须证明其边界数据一致、极小性、单层结构以及关键改进常数对逼近一致，最后证明这些近似解收敛到指定原解。没有这些步骤，“用逼近消去三阶正则性”并不是证明。

后续核心的证明位置如下：层面图、坏点与共同参考高度见 HA1–HA3、HA8–HA11；调和性与强加权梯度收敛见 HA4–HA6；倾斜改进及停止尺度见 HA7、HA11–HA12；跨中心公共方向见 [I2b、I5–I7](iteration-and-directions.md)；最终平移比较见 [DS8–DS12](distance-and-sliding.md) 与 [TB1–TB7](tangent-ball-comparison.md)。最后一块的 Weiss 反应误差仅用势能一阶导数有界，Picone 平方恒等式与弱 Hopf 屏障均不要求势能三阶导数。FE1–FE4 提供这些后续证明的局部估计，并不单独替代它们。
