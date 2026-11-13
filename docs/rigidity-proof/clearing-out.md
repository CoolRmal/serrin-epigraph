# 单相低值清除、自由边界非退化与平面外一致收敛

本章从现有的单相能量极小性、Modica 界和表面尺度单调性出发，补齐“局部积分相位收敛不能直接推出零相最终消失”这一环。只使用势函数的二阶连续性，不使用三阶导数或自由边界的一致曲率界。

## CO1. 能量与固定常数

环境维数记为 n，界面维数记为 d=n−1。

记原尺度能量为

$$J(u,D)=\int_D\left(\frac12|\nabla u|^2+W(u)\mathbf1_{\{u>0\}}\right).$$

本章输入：u 为连续、局部 Lipschitz 的非负函数，取值不超过一，且对值域仍在闭单位区间、与 u 仅有紧支撑差异的局部 Lipschitz 竞争函数满足极小性。

由于势在零处严格正，选取固定常数

$$0<\delta_0<1,\qquad c_0=W(0)/2>0,$$

使

$$W(t)\ge c_0\quad(0\le t\le\delta_0).$$

令

$$F=\max_{[0,\delta_0]}f\ge0.$$

这里反应项在非负小区间非负；所需的关键下界是

$$W(a)-W(b)=-\int_b^a f(t)\,dt\ge-F(a-b)
\quad(0\le b\le a\le\delta_0).\tag{CO1.1}$$

若只从势函数出发，也可把 F 取为其负一阶导数的非负上界。

## CO2. 显式环带屏障

固定正半径 r，令

$$s=r/2,\qquad A_{s,r}=B_r\setminus\overline B_s.$$

对非负数 delta，考虑径向函数 w，其边界值为内零、外 delta，并满足

$$-\Delta w=F\quad\text{在 }A_{s,r}.$$

写径向参数为 rho。直接积分径向方程，取

$$I_{s,r}=\int_s^r t^{1-n}\,dt>0,
\qquad A=\frac{\delta+F(r^2-s^2)/(2n)}{I_{s,r}},$$

$$w(\rho)=\int_s^\rho\left(A t^{1-n}-\frac Fn t\right)dt.$$

由定义内边界值为零，外边界值为 delta；求导并代入径向 Laplacian，即验证方程。若在闭环带内部有严格负的最小值，可把函数减去任意小正倍的平方半径，应用二阶极值检验再送该正数趋零，得到 Laplacian 非正的函数不低于其边界最小值。因此 w 非负；当 F 或 delta 非零时，内法向向外的径向导数也非负。

不需要最优导数常数。因为

$$I_{s,r}\ge(r-s)r^{1-n}=\tfrac12r^{2-n},$$

有

$$w'(s)\le A s^{1-n}
\le 2^n\frac\delta r+\frac{2^{n-1}}nFr
\le2^n\left(\frac\delta r+Fr\right).\tag{CO2.1}$$

屏障在环带内部可能超过 delta，这不影响后面的竞争函数：只在它低于原解处用它替换原解。

## CO3. 低值清除引理

存在只依赖维数、势和上述常数的正数

$$r_*>0,\qquad a_*>0,$$

使得对于任何球心、任何

$$0<r\le r_*,\qquad 0\le u\le a_*r\quad\text{在 }B_r,$$

都必有

$$u\equiv0\quad\text{在 }B_{r/2}.\tag{CO3.1}$$

**证明。** 平移球心至零，取 delta 等于 a 星乘 r，并把 a 星和 r 星选得满足 delta 不超过 delta0。令 w 为 CO2 的屏障。定义竞争函数

$$v=\begin{cases}
0,&|x|\le s,\\
\min\{u,w\},&s<|x|<r,\\
u,&|x|\ge r.
\end{cases}$$

内球面上屏障为零；外球面上屏障为 delta，而原解不超过 delta。因此三个分段的迹一致，函数连续且局部 Lipschitz，取值介于零与 u 之间。它与 u 的差支撑于闭 r 球，故是允许的竞争函数。

在环带令

$$z=(u-w)^+.$$

环带中只有 z 为正处的能量发生改变。在此处，原解和屏障都在闭 delta 区间中，且

$$\frac12(|\nabla u|^2-|\nabla w|^2)
=\nabla w\cdot\nabla z+\frac12|\nabla z|^2
\ge\nabla w\cdot\nabla z.$$

加上 CO1.1 并积分，极小性给出

$$0\ge J(u,B_r)-J(v,B_r)
\ge J(u,B_s)+\int_{A_{s,r}}(\nabla w\cdot\nabla z-Fz).$$

屏障方程和环带积分分部给出：外边界的 z 为零，内边界的 z 为 u，环带的内边界外法向为负径向，因此

$$\int_{A_{s,r}}\nabla w\cdot\nabla z
=F\int_{A_{s,r}}z-w'(s)\int_{\partial B_s}u.$$

上式对 Lipschitz z 可由其光滑逼近得到：体积分按一阶 Sobolev 收敛，边界迹按连续/Lipschitz 逼近收敛。所有环带边界光滑，屏障及其法向导数有界。

令

$$I=\int_{B_s}\left(\frac12|\nabla u|^2+c_0\mathbf1_{\{u>0\}}\right).$$

势的低值下界使 I 不超过原解内球能量，前面两个体积项恰好抵消，得到

$$I\le w'(s)\int_{\partial B_s}u.\tag{CO3.2}$$

剩下的球面项不能直接丢弃。对向量场 xu 使用散度公式并除以 s，得到

$$\int_{\partial B_s}u
=\frac ns\int_{B_s}u+\frac1s\int_{B_s}x\cdot\nabla u
\le\frac{n\delta}s|B_s\cap\{u>0\}|+\int_{B_s}|\nabla u|.$$

局部 Lipschitz 非负函数在其零点集合上几乎处处梯度为零：在函数可微的零点处它取得最小值，导数必须为零。因此下面的点态估计可以只在正相上使用：

$$|p|\le\frac{\frac12|p|^2+c_0}{\sqrt{2c_0}}.$$

这个不等式等价于平方

$$\bigl(|p|-\sqrt{2c_0}\bigr)^2\ge0.$$

故

$$\int_{\partial B_s}u
\le\left(\frac1{\sqrt{2c_0}}+\frac{n\delta}{s c_0}\right)I.\tag{CO3.3}$$

结合 CO2.1–CO3.3，使用 delta 除 r 等于 a 星、s 等于 r 的一半，得

$$I\le
2^n(a_*+Fr_*)\left(\frac1{\sqrt{2c_0}}+\frac{2na_*}{c_0}\right)I.$$

先选足够小的正 a 星，使第二个括号有固定有限上界并使只含 a 星的乘积小于四分之一；再选足够小的正 r 星，使剩余 F 项小于四分之一，并使 a 星乘 r 星不超过 delta0。于是右侧系数至多为二分之一。I 有限且非负，故 I 等于零。正相在内球的体积为零；若内球一点函数值正，由连续性某个小球上函数也正，将产生正体积，矛盾。所以函数在整个内球恒零。证毕。

## CO4. 自由边界附近必出现固定正层值

把 CO3 固定在半径 r 星。若一个自由边界点中心的该球上函数处处不超过 a 星乘 r 星，则 CO3 使半径减半的球恒零，与该点是正相边界矛盾。因此

$$\sup_{B_{r_*}(x_0)}u>a_*r_*
\quad(x_0\in\partial\{u>0\}).$$

取固定内部层值

$$a_0=\tfrac12\min\{a_*r_*,1/2\}>0.$$

边界点值为零，附近有点超过 a0；连接线段上的连续性给出一个 a0 层面点，且距该自由边界点小于 r 星。

对缩放解

$$v_\varepsilon(x)=u(x/\varepsilon),$$

同一结论变为：每个自由边界点距离某个 a0 层面点至多为 r 星乘 epsilon。这一常数与边界点无关。它不依赖原图形的全局曲率界。

## CO5. 内部层值的能量下界与大尺度传播

假定正相中的 Modica 估计成立。令

$$M=\max_{[0,1]}\sqrt{2W}<\infty.$$

零延拓的梯度几乎处处长度不超过 M，因此它全局 M-Lipschitz：沿线段可用局部 Lipschitz 函数的弱梯度上界和光滑卷积证明相同的差值界。缩放后梯度上界为 M 除 epsilon。

固定两个正数 a、b，使 a 小于一减 b。若某点满足

$$a\le v_\varepsilon(x)\le1-b,$$

则在半径

$$\rho_\varepsilon=\frac{\min\{a,b\}}{2M}\varepsilon$$

的球上，解值介于 a 的一半与一减 b 的一半之间。若 M 为零则势在闭单位区间恒零，与零点正势矛盾，故上述除法合法。

势在这个紧区间的最小值严格正，记为 w 星。因此缩放能量密度满足

$$e_\varepsilon=\frac\varepsilon2|\nabla v_\varepsilon|^2
+\varepsilon^{-1}W(v_\varepsilon)\mathbf1_{\{v_\varepsilon>0\}}
\ge w_*/\varepsilon\quad\text{于 }B_{\rho_\varepsilon}(x).$$

于是该球的能量至少为固定正常数乘 epsilon 的 d 次方，归一化表面密度至少为固定正数。已有的、任意中心成立的表面尺度单调性遂给出

$$\int_{B_r(x)}e_\varepsilon\ge c(a,b)r^d
\quad(r\ge\rho_\varepsilon).\tag{CO5.1}$$

CO4 还把此估计传至自由边界中心：只需使半径至少为一个固定常数乘 epsilon，用层面点的较小球包含在边界中心球中。此处不要求自由边界处直接有统一二阶导数估计。

## CO6. 平面外的能量消失：只用已有球质量与原函数通量

假设同一缩放序列局部积分收敛到半空间示性函数，并且原点球能量满足已有的精确极限

$$\int_{B_s}e_{\varepsilon_j}\longrightarrow\sigma\omega_d s^d
\quad(s>0),\qquad H=\{x:x\cdot e>0\}.$$

原函数

$$p_j=\int_0^{v_{\varepsilon_j}}\sqrt{2W(t)}\,dt$$

局部积分收敛到 sigma 乘半空间示性函数，且由平方配方

$$|\nabla p_j|\le e_{\varepsilon_j}.$$

固定一个与边界平面不交的紧集 K，取原点球 B_s 严格包含它。对任意光滑截断 eta，其取值介于零与一、支撑紧含于该球并避开 K，有

$$\int_K e_{\varepsilon_j}+\int\eta\,e\cdot\nabla p_j
\le\int_{B_s}e_{\varepsilon_j}.$$

分部积分及局部积分收敛给出第二项的极限为

$$\sigma\int_{e^\perp}\eta\,d\mathcal H^d.$$

因为 K 与平面有正距离，可以选 eta 在平面与稍小球的交集附近等于一，同时避开 K。让稍小半径上升至 s，平面上截断积分可任意接近单位 d 维球体积乘 s 的 d 次方。因此

$$\limsup_j\int_K e_{\varepsilon_j}\le0.$$

被积函数非负，故该积分趋零。没有预先使用任意区域上的能量测度收敛。

## CO7. 层面、自由边界与两侧一致极限

若在某个与平面有正距离的紧集内存在固定内部值域的点，取子列及小球，使这些球都位于另一个与平面不交的固定紧集内。CO5.1 在这些固定半径球上给出严格正、与序列无关的能量下界，与 CO6 矛盾。因此任意固定内部层值区间的点最终都离开每个这样的紧集。

在正半空间内固定闭球，其略大闭球仍位于正半空间。给定 b 正且足够小，由局部积分趋一，可在球内找到解值超过一减 b 的点。若另一点的解值不超过一减二倍 b，连接线段上必有一个固定内部层值；这与上一段在该闭球上排除内部层值矛盾。因此解在正半空间的每个紧集上一致趋一。

在负半空间同理：局部积分趋零确保球内存在小于任意固定小值的点；若另一点超过该小值的两倍，中间值定理给出被排除的内部层值。故负半空间紧集上一致趋零。

自由边界最终也不能出现在任何与平面有正距离的紧集内：CO4 会在距离仅为固定常数乘 epsilon 的地方产生固定 a0 层值，仍与前述层面排除矛盾。

更直接地，负半空间紧集取一个略大紧邻域。其上解一致趋零；足够大的序列指标使其小于 a 星乘 r 星。对紧集每一点应用尺度化 CO3，使用半径 r 星乘 epsilon 的球；这些球全部位于较大邻域。于是解在该紧集上最终恒零。

因此得到了需要的完整两侧结论：正相侧一致趋一，零相侧最终恒零，固定内部层面及自由边界在有界区域内被任意窄的平面条带捕获。若还要双向 Hausdorff 收敛，平面的每点邻域分别含有上侧正值点和下侧零点；连接线段必经过正相边界，给出反向逼近。

## 形式化顺序

CO2 的径向屏障是显式积分，无须新的 PDE 存在定理。CO3 使用现有闭值域局部 Lipschitz 极小性，但需补齐最小值竞争函数与环带积分分部的接口。CO5 复用任意中心的表面能量单调性；CO6 复用原函数局部积分收敛和原点球质量等式；CO7 只需紧集覆盖、连续性和缩放。

这些结果补齐的是清除与位置控制，不替代小倾斜好集上的单层图形、调和近似和倾斜改进。后者在独立章节继续证明。
