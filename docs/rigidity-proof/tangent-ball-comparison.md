# 外侧零球接触的精确斜率与有序平移的边界排除

本章只在已经构造出一对相反的切球时使用边界比较。它不把任意两个可能奇异的单相自由边界的强比较原理作为前提。关键是：外侧零球、Modica 的全局 Lipschitz 界和应力驻定性，足以把接触点的每个微观极限确定为同一个平面剖面。然后在另一函数的正相内球上，对函数差使用普通的弱 Hopf 比较。

## TB1. 输入、零延拓和用于极限的恒等式

环境维数至少为二。势满足本项目已恢复的条件；特别地，在闭单位区间上有

$$
W\in C^2([0,1]),\qquad W(0)>0,\qquad W'=-f\le0.
$$

记

$$
\kappa=\sqrt{2W(0)},\qquad L_f=\max_{[0,1]}|f'|.
$$

设 U 是原解的零延拓，或它的局部一致平移极限。本章使用以下已证明性质：U 取值于闭单位区间，连续且全局 kappa-Lipschitz；在正相内满足方程；在整个空间满足应力驻定性及 CO3 的小半径清除结论。写为

$$
\Omega=\{U>0\},\qquad \Delta U=W'(U)\quad\text{在 }\Omega,
\tag{TB1.1}
$$

$$
\int\left[
\left(\frac12|\nabla U|^2+W(U)\mathbf1_\Omega\right)\operatorname{div}X
-\nabla U\cdot DX\nabla U
\right]=0
\quad(X\in C_c^1(\mathbb R^n;\mathbb R^n)).
\tag{TB1.2}
$$

Lipschitz 常数确实可取 kappa：Modica 给出梯度长度不超过平方根二倍 W，而 W 在此区间不增。零相上的梯度几乎处处为零；卷积后沿线段积分，再令卷积尺度趋零，即把几乎处处的梯度界变成整个空间的同一 Lipschitz 界。

下面给出后面反复使用的标量恒等式，避免在不光滑自由边界上未经说明积分分部。任取紧支撑光滑函数 eta。在正相的弱方程中测试

$$
(U-\delta)^+\eta,\qquad \delta>0.
$$

其支撑在 eta 的支撑与闭集 U 不小于 delta 的交集内，因此紧包含于正相；Sobolev 测试可由光滑逼近取得。令 delta 下降到零。U 为 Lipschitz，且其零集上梯度几乎处处为零，故支配收敛给出

$$
\int\eta|\nabla U|^2
+\int U\nabla U\cdot\nabla\eta
+\int U W'(U)\eta=0.
\tag{TB1.3}
$$

最后一项可不写正相指示函数，因为 U 在零相等于零。这个论证没有使用自由边界光滑性。

本章也使用零延拓的分布不等式

$$
\Delta U\ge-f(U).
\tag{TB1.4}
$$

对原来的光滑解，正相中的等式与自由边界向内斜率为 kappa 给出非负的界面分布项；零相中右侧为负的 f(0)，而 f(0) 非负，所以不等式成立。对非负紧支撑测试函数逐项积分即可验证符号。局部一致平移极限保持这个不等式，因为 f 连续，而分布 Laplacian 直接由函数与测试函数的 Laplacian 配对定义。

### 平移极限为何仍可使用这些输入

为核对 TB1 的适用范围，设原解的平移序列局部一致收敛到 U。统一 Lipschitz 界直接传递；任意紧包含于 U 正相的集合上，原方程的弱极限给出 TB1.1，内部椭圆正则性给出经典方程。CO3 的严格版本也传递：若某球上 U 严格小于清除阈值，近似函数最终满足该阈值，因而在半球上恒零。

在 U 几乎处处的零点，Lipschitz 函数可微，且因其非负，导数为零。因此在这样的点 x，

$$
\sup_{B_r(x)}U=o(r).
$$

对足够小的 r 使用刚才传递的严格清除结论，知 x 实际属于零相的内部。所以 U 的零集除去其内部后是零体积集。在正相的每一点，近似函数最终为正；在零相的每个内点，清除使它们在一个小邻域最终恒零。于是相位指示函数几乎处处、进而局部一阶可积收敛。

梯度先因统一界而弱平方可积收敛。把 TB1.3 应用于近似函数和 U。函数局部一致收敛、梯度弱收敛、连续函数 s 乘 W 的一阶导数的收敛，使每个非负光滑 eta 对应的梯度平方积分收敛。弱收敛加平方范数收敛给出紧集上的强平方可积收敛。故 TB1.2 中的梯度二次项和势能项均收敛，应力驻定性传给 U。以上说明并不要求平移极限的自由边界先有任何光滑性。

## TB2. 小尺度非退化和微观紧性

平移接触点至原点，并设它属于正相边界，故 U(0) 等于零。CO3 提供固定正常数 a星、r星。对每个不超过 r星 的正半径，必有

$$
\sup_{B_r}U>a_*r.
\tag{TB2.1}
$$

否则 CO3 会把半径减半的球清为空正相，与原点属于正相边界矛盾。对已取平移极限的函数，可以把 a星 先减半；上一节的严格清除版本给出相同结论。

给定任意趋零正数列，定义

$$
r_j\downarrow0,\qquad U_j(x)=\frac{U(r_jx)}{r_j}.
\tag{TB2.2}
$$

它们在整个空间仍为 kappa-Lipschitz，原点取零，且在每个固定球上绝对值不超过 kappa 乘该球半径。Arzela–Ascoli 和逐球对角线选择给出局部一致收敛的子序列，记极限为 V。梯度在每个紧球上有弱平方可积收敛。TB2.1 保证

$$
\sup_{\overline B_1}V\ge a_*>0,
\tag{TB2.3}
$$

所以极限不是零函数。在其正相的每个紧集上，近似函数最终为正，且

$$
\Delta U_j=r_jW'(r_jU_j)\longrightarrow0.
$$

右侧在该紧集一致趋零。因此 V 在其正相内弱调和，进而光滑调和。下面从驻定性证明它恰为一次齐次；不能仅因原点是自由边界点就预设这个结论。

## TB3. 含反应项的精确 Weiss 恒等式

记

$$
A(r)=\int_{B_r}|\nabla U|^2,\qquad
B(r)=\int_{B_r}W(U)\mathbf1_\Omega,
$$

$$
E(r)=A(r)+2B(r),\qquad
H(r)=\int_{\partial B_r}U^2,
\qquad
\mathcal W(r)=r^{-n}E(r)-r^{-n-1}H(r).
\tag{TB3.1}
$$

这些函数在每个不含零半径的紧区间绝对连续。关于球面积分的公式可先用球面参数化、Lipschitz 函数的沿射线链式法则及 Fubini 得到；下面各微分恒等式对几乎处处半径成立。

在 TB1.2 中代入径向场

$$
X(x)=\zeta(|x|)x.
$$

其散度为 n 倍 zeta 加半径乘 zeta 导数，其导数矩阵为 zeta 乘恒等矩阵加 zeta 导数除半径乘 x 张量 x。用径向光滑截断逼近球的指示函数，得到

$$
rE'(r)=(n-2)A(r)+2nB(r)
+2r\int_{\partial B_r}(\partial_rU)^2.
\tag{TB3.2}
$$

同样用径向截断逼近 TB1.3，得到

$$
A(r)+\int_{B_r}U W'(U)
=\int_{\partial B_r}U\partial_rU.
\tag{TB3.3}
$$

球面参数化还给出

$$
H'(r)=\frac{n-1}{r}H(r)
+2\int_{\partial B_r}U\partial_rU.
\tag{TB3.4}
$$

现在直接微分 TB3.1，并用 TB3.2–TB3.4 消去体积梯度项：

$$
\begin{aligned}
\mathcal W'(r)
={}&r^{-n-1}\left[-nE+rE'+\frac2rH
-2\int_{\partial B_r}U\partial_rU\right]\\
={}&2r^{-n-1}\left[
r\int_{\partial B_r}(\partial_rU)^2
-A-\int_{\partial B_r}U\partial_rU+\frac Hr
\right]\\
={}&2r^{-n}\int_{\partial B_r}
\left(\partial_rU-\frac Ur\right)^2
+2r^{-n-1}\int_{B_r}U W'(U).
\end{aligned}
\tag{TB3.5}
$$

这个恒等式的最后一项带正的系数乘 U 与 W 的一阶导数；在当前势的符号下它非正，不能省略。

因为原点取零且 U 为 kappa-Lipschitz，在半径 r 的球上 U 不超过 kappa 乘 r。令 M 为 W 的一阶导数在闭单位区间的绝对值上界，则

$$
\left|2r^{-n-1}\int_{B_r}U W'(U)\right|
\le2\kappa M\omega_n=:C_0.
\tag{TB3.6}
$$

因此加上 C0 乘 r 的 Weiss 量单调不减。梯度界、势能有界以及 U 不超过 kappa 乘半径，分别给 TB3.1 两项统一的上下界。所以

$$
\lim_{r\downarrow0}\mathcal W(r)=\mathcal W(0+)
$$

存在且有限。这里不使用势的三阶导数，也不需要对自由边界曲率求导。

## TB4. 不预设能量强收敛就取得一次齐次

对任意固定正数 a 小于 b，把 TB3.5 从 a 倍 rj 积分至 b 倍 rj。TB3.6 和 Weiss 极限给出

$$
\int_{ar_j}^{br_j}t^{-n}
\int_{\partial B_t}
\left(\partial_tU-\frac Ut\right)^2\,dt
\longrightarrow0.
\tag{TB4.1}
$$

按 TB2.2 换元，左侧恰为

$$
\int_a^b\rho^{-n}
\int_{\partial B_\rho}
\left(\partial_\rho U_j-\frac{U_j}{\rho}\right)^2\,d\mathcal H^{n-1}\,d\rho.
$$

在固定环带上权重有正的上下界，函数一致收敛且梯度弱平方可积收敛。平方范数的弱下半连续性表明，对 V 的同一积分为零。对有理端点的可数个环带应用这个结论，再用 Fubini，得到几乎每条射线上

$$
\partial_\rho V(\rho\theta)=\frac{V(\rho\theta)}\rho
\quad\text{几乎处处 }\rho>0.
$$

沿射线的局部绝对连续性于是给出 V 除以 rho 为常数。V 连续，所以几乎处处的齐次等式推广到所有点与所有正缩放：

$$
V(tx)=tV(x)\qquad(t>0).
\tag{TB4.2}
$$

这个证明只用了弱梯度收敛；因此不存在先假定微观自由边界正则性、再据此证明齐次性的循环。

## TB5. 支撑在半空间内的一次齐次极限必为线性正部

现在假定原函数在一个外侧切球上为零。经旋转记该条件为

$$
B_R(-Re_n)\subset\{U=0\},\qquad R>0.
\tag{TB5.1}
$$

固定最后坐标为负的 x。对充分大 j，

$$
|r_jx+Re_n|^2<R^2
\quad\Longleftrightarrow\quad
r_j|x|^2+2R x_n<0.
$$

所以该点的微观极限为零。连续性给出 V 在闭负半空间为零；全局 Lipschitz 界进一步给出

$$
0\le V(x)\le\kappa x_n^+.
\tag{TB5.2}
$$

写

$$
V(\rho\theta)=\rho g(\theta),\qquad
S_+=\{\theta\in\mathbb S^{n-1}:\theta_n>0\},
\qquad \phi(\theta)=\theta_n.
$$

g 为 Lipschitz、非负，在闭负半球为零，并在赤道上取零。因而其在正半球的限制属于零边界迹的一阶 Sobolev 空间；也可将它在赤道附近截去后光滑逼近，因为 g 不超过 kappa 乘到赤道的常数倍距离。正半球上有

$$
0\le g\le\kappa\phi.
\tag{TB5.3}
$$

先取得精确的球面能量等式。在 V 的正相内调和方程中测试正部截断

$$
(V-\delta)^+\eta(|x|),
$$

其中 eta 支撑在不包含原点的紧环带内。令 delta 下降到零，得到

$$
\int\eta|\nabla V|^2+V\nabla V\cdot\nabla\eta=0.
$$

一次齐次性给出梯度平方为 g 平方加球面梯度平方。代入极坐标并用

$$
\int_0^\infty\rho^n\eta'(\rho)\,d\rho
=-n\int_0^\infty\rho^{n-1}\eta(\rho)\,d\rho,
$$

可消去非零径向因子，得到

$$
\int_{S_+}|\nabla_S g|^2
=(n-1)\int_{S_+}g^2.
\tag{TB5.4}
$$

下面把半球的等号情形直接算出。坐标函数满足

$$
-\Delta_S\phi=(n-1)\phi.
$$

对正数 epsilon 令 a 等于 phi 加 epsilon。展开 g 等于 a 乘 g 除 a 的梯度平方，并将交叉项积分分部；g 的零边界迹使边界项为零。得到

$$
\int_{S_+}|\nabla_Sg|^2
=\int_{S_+}a^2\left|\nabla_S\frac ga\right|^2
+(n-1)\int_{S_+}\frac\phi{\phi+\varepsilon}g^2.
\tag{TB5.5}
$$

这个等式对零边界迹光滑逼近成立并传给 g；对固定 epsilon，分母严格为正，所有系数与所需导数有界。结合 TB5.4，有

$$
\int_{S_+}(\phi+\varepsilon)^2
\left|\nabla_S\frac g{\phi+\varepsilon}\right|^2
=(n-1)\int_{S_+}\frac\varepsilon{\phi+\varepsilon}g^2
\longrightarrow0.
\tag{TB5.6}
$$

右侧由支配收敛趋零。在任意紧包含于正半球的集合上，g 除以 phi 加 epsilon 的梯度平方可积收敛到 g 除以 phi 的梯度，故后者为零。正半球连通，局部 Sobolev 常数性和连续性说明 g 除以 phi 是一个全局常数。TB2.3 与 TB5.3 给出

$$
V(x)=c x_n^+,\qquad 0<c\le\kappa.
\tag{TB5.7}
$$

这一推导不引用球面区域第一特征值的严格单调性，也不假定极限正相的边界光滑；整个半球正相和光滑性都是等号计算的结果。

## TB6. 平面幅度由驻定性确定，得到全族精确斜率

还不能把 TB5.7 中的 c 直接替换为 kappa。下面验证极限应力，并从其平面界面项确定幅度。

在严格正半空间，局部一致收敛到 c 倍最后坐标说明 Uj 最终为正；在严格负半空间，TB5.1 的球包含说明 Uj 最终为零。因此

$$
\mathbf1_{\{U_j>0\}}\longrightarrow\mathbf1_{\{x_n>0\}}
\quad\text{几乎处处且局部一阶可积}.
\tag{TB6.1}
$$

TB1.3 的缩放式为

$$
\int\eta|\nabla U_j|^2
=-\int U_j\nabla U_j\cdot\nabla\eta
-r_j\int U_jW'(r_jU_j)\eta.
\tag{TB6.2}
$$

最后一项在每个紧集趋零；第一项由函数一致收敛和梯度弱收敛趋向 V 对应的项。V 的截断测试恒等式说明这个极限正好是 eta 加权的梯度平方积分。因此弱收敛加范数收敛使梯度在每个紧集强平方可积收敛。与 TB6.1 一起，这足以通过缩放后的应力驻定性：

$$
\int_{\{x_n>0\}}
\left[\left(\frac{c^2}2+W(0)\right)\operatorname{div}X
-c^2\partial_nX_n\right]=0.
\tag{TB6.3}
$$

取仅有最后分量的测试场。对最后坐标积分，得到

$$
\left(W(0)-\frac{c^2}2\right)
\int_{\mathbb R^{n-1}}X_n(y,0)\,dy=0.
$$

最后的积分可以任取非零值，故 c 平方等于二倍 W(0)。由于 c 为正，必有 c 等于 kappa。

初始趋零数列完全任意，而它的每个收敛子序列都得到同一个极限。因此不是仅有一列微观半径成立，而是全族成立：对每个固定紧集 K，

$$
\frac{U(r\,\cdot)}r\longrightarrow\kappa x_n^+
\quad\text{在 }C(K)\text{ 中，当 }r\downarrow0.
\tag{TB6.4}
$$

若不成立，可选一个固定正误差及违反它的半径列，TB2 的紧性又给出同一个极限，矛盾。旋转、平移回来得到本章的精确接口：

$$
\boxed{\quad
p\in\partial\{U>0\},\quad
B_R(p-R\nu)\subset\{U=0\}
\quad\Longrightarrow\quad
U(p+s\nu)=\kappa s+o(s)\quad(s\downarrow0).
\quad}
\tag{TB6}
$$

这里只要求 nu 为单位向量；没有假定 p 是自由边界的正则点。

## TB7. 相反切球使有序的两个函数不能严格接触

设 U、V 都满足 TB1 的性质，且

$$
0\le U\le V,\qquad U(0)=V(0)=0,
$$

$$
B_R(-R\nu)\subset\{U=0\},\qquad
B_R(R\nu)\subset\{V>0\},\qquad
0\in\partial\{U>0\}.
\tag{TB7.1}
$$

在 V 的正相球内令 w 等于 V 减 U。由 V 的经典方程和 U 的分布不等式 TB1.4，

$$
\Delta w\le f(U)-f(V)\le L_f w,
\qquad w\ge0.
\tag{TB7.2}
$$

这条不等式在整个球内成立，包含 U 的自由边界；所以不需要在那里对 w 作经典二次求导。要么 w 在该球恒零，要么它在球内处处严格正。后一断言可以直接用下面同一个环带屏障证明：若某点取正值，连续性先给一个闭小球上的严格正下界；取任意同心、紧包含于原球的较大球，在二者之间的环带应用下段的指数屏障和负部测试。内球面取严格正比较值，外球面只用 w 非负，便使整个外球内部严格为正。任意两内点可以用留在原球内的线段相连，其紧线段由有限个相交内球覆盖；逐球重复该论证把正性传到目标点。内外半径不必恰为一与二之比，只须选 A 使所写的括号在相应环带非负。因此这里也不需要另行调用弱 Harnack 定理。

在严格正的情形，下面写出需要的 Hopf 下界。球心记为 z 等于 R 倍 nu。在半径介于 R 除二与 R 的闭环带上取

$$
\beta(x)=e^{-A|x-z|^2}-e^{-AR^2}.
$$

它在外球面为零、内球面严格正，且

$$
(\Delta-L_f)\beta
=\left(4A^2|x-z|^2-2An-L_f\right)e^{-A|x-z|^2}
+L_f e^{-AR^2}.
$$

选足够大的固定 A，使括号在该环带非负。w 在内球面连续且严格正，其最小值为正，所以可选正常数 b，使 w 至少为 b 倍 beta 于内球面；外球面该比较由 w 非负成立。函数 w 减 b 倍 beta 满足算子 Delta 减 Lf 作用后非正。若它有负部，用该负部测试弱不等式，即得到负部的梯度平方加 Lf 倍平方积分不超过零，所以负部为零。于是整个环带都有 w 不小于 b 倍 beta。

沿内法线令 x 等于 s 倍 nu，其中 s 趋零为正。直接微分指数给出

$$
\beta(s\nu)=2AR e^{-AR^2}s+O(s^2),
$$

故存在正常数 b星，使充分小正 s 满足

$$
V(s\nu)-U(s\nu)\ge b_*s.
\tag{TB7.3}
$$

另一方面，V 在原点取零且为 kappa-Lipschitz，TB6 又给出 U 的斜率，所以

$$
V(s\nu)\le\kappa s,
\qquad
U(s\nu)=\kappa s+o(s).
$$

两式相减只允许上界为小于 s 的低阶量，与 TB7.3 矛盾。

因此相反切球条件下，w 必须在 V 的该正相球上恒零。在后续平移应用中，正相连通性和内部强比较把这个正相开集上的相等推广到整个相应正相，再由既有的粗锥形几何排除非零平移周期。这个全局传播在后续章节完成；本章的局部结论本身不假定全局边界正则性。

## 核对范围与形式化落点

TB3 是径向应力测试、标量截断测试和绝对连续函数微分；TB4 是带权平方范数弱下半连续性；TB5 是球面坐标函数方程及带正分母的 Picone 平方恒等式；TB6 是局部强梯度收敛和分布应力极限；TB7 只需要线性弱最大值原理与显式环带屏障。

本章没有使用一般的奇异自由边界强比较定理。相关一般理论的范围可对照 [Edelen–Spolaor–Velichkov 的 Theorem 1.1](https://arxiv.org/abs/2205.00401)；这里的额外相反切球由平移序集合的几何构造提供，使上述独立计算足够。Weiss 型径向量在这里的含势能恒等式为 TB3.5，不能用无反应项版本替换后漏掉最后一项。
