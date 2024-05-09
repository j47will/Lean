import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Ring.Commute
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Polynomial.Coeff
import Mathlib.RingTheory.Ideal.Quotient
open BigOperators Polynomial


-- ########### definition ###########
section definition

class DeltaRing (A: Type u)[CommRing A](p: ℕ)(delta: A → A)  where
  (map_zero: delta (0) = 0)
  (map_one: delta (1) = 0)
  (map_mul: ∀{x y}, delta (x*y) = (x^p * delta (y)) + (y^p * delta (x)) + (p * delta (x) * delta (y)))
  (map_add: ∀{x y}, delta (x+y) = (delta (x) + delta (y)) - ∑ i in Finset.Ioo 0 (p), (x^(i:ℕ) * (y^(p-i)) * ((Nat.choose p i)/p: ℕ)))



lemma Delta_one {A: Type}[CommRing A](p: ℕ)(delta: A → A)[DeltaRing A p delta] :
  delta 1 = 0 := by
  exact DeltaRing.map_one p

lemma Delta_zero  {A: Type}[CommRing A](p: ℕ)(delta: A → A)[DeltaRing A p delta] :
  delta 0 = 0 := by
  exact DeltaRing.map_zero p

lemma Delta_mul {A: Type}[CommRing A](x y: A)(p: ℕ)(delta: A → A)[DeltaRing A p delta] :
  delta (x*y) = (x^p * delta (y)) + (y^p * delta (x)) + (p * delta (x) * delta (y)) := by
  exact DeltaRing.map_mul

lemma Delta_add {A: Type}[CommRing A](x y: A)(p: ℕ)(delta: A → A)[DeltaRing A p delta] :
  delta (x+y) = (delta (x) + delta (y)) - ∑ i in Finset.Ioo 0 (p), (x^(i:ℕ) * (y^(p-i)) * ((Nat.choose p i)/p: ℕ)) := by
  exact DeltaRing.map_add

end definition


-- ########### example 1 ###########
section example1

lemma add_add_mul (a b c d: ℚ): (b+c+d)*a = b*a + c*a + d*a := by
  ring

example (p: ℕ) (hp: Nat.Prime p): DeltaRing ℚ p fun n => (n-n^p)/p where
  map_zero:= by
    rw [zero_pow, sub_self, zero_div]
    exact Nat.Prime.pos hp

  map_one:= by
    simp only [one_pow, sub_self, zero_div]

  map_mul:= by
    intro x y
    rw [div_eq_iff_mul_eq, add_add_mul]
    repeat rw [mul_right_comm, mul_assoc, mul_div_cancel']
    ring
    repeat' rw [ne_eq, Nat.cast_eq_zero]
    repeat' exact Nat.Prime.ne_zero hp

  map_add:= by
    intro x y
    simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, ge_iff_le, Nat.isUnit_iff]
    rw [div_eq_iff_mul_eq,sub_eq_add_neg,add_add_mul,div_mul_cancel,div_mul_cancel,add_pow_prime_eq hp]
    ring
    repeat' rw [ne_eq, Nat.cast_eq_zero]
    repeat' exact Nat.Prime.ne_zero hp

end example1


-- ########### example 2 ###########
section example2

lemma mul_add_add {A: Type u}[CommRing A](a b c d: A): a*(b+c+d) = a*b+a*c+a*d := by
  ring

lemma jfjk (b: ℤ)(p: ℕ)(hp: Nat.Prime p) : ↑p * ((b - b ^ p) / ↑p) = ((b - b ^ p)) := by
  refine Int.mul_ediv_cancel' ?H
  rw [← ZMod.int_cast_eq_int_cast_iff_dvd_sub]
  rw [Int.cast_pow]
  haveI : Fact (Nat.Prime p):= by
    exact { out := hp }
  apply ZMod.pow_card

lemma abcd (a b c d e: ℤ) : a-b+(c-d)-e = a+c-(b+d+e) := by
  ring

example (p : ℕ)(hp : Nat.Prime p): DeltaRing ℤ p fun n => (n-n^p)/p where
  map_zero := by
    rw [zero_pow, zero_sub,neg_zero, EuclideanDomain.zero_div]
    exact Nat.Prime.pos hp

  map_one := by
    rw [one_pow, sub_self, EuclideanDomain.zero_div]

  map_mul := by
    intro x y
    rw [Int.ediv_eq_iff_eq_mul_right]
    rw [jfjk _ _ hp,mul_add_add]
    repeat rw [mul_left_comm,jfjk _ _ hp]
    ring
    refine Iff.mpr Int.ofNat_ne_zero ?H.a
    exact Nat.Prime.ne_zero hp
    rw [← ZMod.int_cast_eq_int_cast_iff_dvd_sub,Int.cast_pow]
    haveI : Fact (Nat.Prime p):= by
      exact { out := hp }
    apply ZMod.pow_card

  map_add := by
    simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, ge_iff_le, Int.ofNat_ediv]
    intro x y
    rw [Int.ediv_eq_iff_eq_mul_right]
    symm
    rw [sub_eq_add_neg,mul_add_add,jfjk _ _ hp,jfjk _ _ hp,mul_neg,← sub_eq_add_neg,abcd,Commute.add_pow_prime_eq hp]
    rfl
    exact Commute.all x y
    refine Iff.mpr Int.ofNat_ne_zero ?H.a
    rw [← ZMod.int_cast_eq_int_cast_iff_dvd_sub,Int.cast_pow]
    haveI : Fact (Nat.Prime p):= by
      exact { out := hp }
    apply ZMod.pow_card

end example2

-- ########### example 3 ###########
section example3


lemma torsion_free_dvd (a b : A)[CommRing A](ht: ∀x:A, p*x=0 ↔ x=0): p * a = p * b ↔ a = b:= by
  apply Iff.intro
  intro ha
  rw [← sub_eq_zero] at ha
  rw [← mul_sub] at ha
  rw [ht] at ha
  rw [sub_eq_zero] at ha
  exact ha
  intro ha
  simp [ha]


lemma mul_eq_zero_iff_eq_zero_poly (h p:ℤ[X])(hp: p ≠ 0) : p*h=0 ↔ h=0 := by
  rw [mul_eq_zero]
  exact or_iff_right hp

variable (g : ℤ[X])(p:ℕ)

noncomputable section
def mymap : ℤ[X] →  ℤ[X] := (fun (f : ℤ[X]) => (f.sum fun n a => C (a) * (X^p + (p : ℤ[X])*g) ^ (n)) - f^p)

lemma mymap_div_p (f : ℤ [X]) : ∃ (h : ℤ[X]), mymap g p f = (p : ℤ[X])  * h := by
  sorry

def mydelta : ℤ[X] → ℤ[X] := by
  intro f
  have Hyp := mymap_div_p g p f
  let h:= Hyp.choose
  refine h

-- f - x^p = p * δ
lemma mylem (f : ℤ [X]) : mymap g  p f = p * (mydelta g p f) := by
  rw [mydelta]
  have Hyp := mymap_div_p g p f
  have := Hyp.choose_spec
  rw [← this]

lemma mylem2 : (mymap g p 1) = 0:= by
  rw [mymap]
  simp only [eq_intCast, one_pow]
  rw [sum, Finset.sum_eq_single 0 ]
  simp only [coeff_one_zero, Int.cast_one, pow_zero, mul_one, sub_self]
  intro b _ hb0
  simp only [mul_eq_zero, Int.cast_eq_zero]
  left
  have := coeff_one (R := ℤ) b
  rw [this]
  simp only [ite_eq_right_iff]
  intro hB
  exact hb0 hB.symm
  simp only [mem_support_iff, coeff_one_zero, ne_eq, not_true, Int.cast_one, pow_zero, mul_one, one_ne_zero,
    IsEmpty.forall_iff]


example (p : ℕ)(hp: Nat.Prime p): DeltaRing ℤ[X] p (mydelta g p) where
  map_zero := by
    have := mylem g p 0
    rw [mymap] at this
    simp only [eq_intCast, sum_zero_index, ne_eq, zero_sub] at this
    rw [zero_pow,neg_zero] at this
    symm at this
    rw [mul_eq_zero_iff_eq_zero_poly] at this
    exact this
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Nat.Prime.ne_zero hp
    exact Nat.Prime.pos hp

  map_one := by
    have := mylem g p 1
    rw [mylem2] at this
    symm at this
    rw [mul_eq_zero_iff_eq_zero_poly] at this
    exact this
    simp only [ne_eq, Nat.cast_eq_zero]
    exact Nat.Prime.ne_zero hp

  map_mul := by
    intro a b
    have := mylem g p (a*b)

    rw [← torsion_free_dvd (p := (p : ℤ[X])) (mydelta g p (a * b)) (a ^ p * mydelta g p b + b ^ p * mydelta g p a + ↑p * mydelta g p a * mydelta g p b)]
    symm
    rw [mul_add_add]
    have this2 : ↑p * (a ^ p * mydelta g p b) + ↑p * (b ^ p * mydelta g p a) + ↑p * (↑p * mydelta g p a * mydelta g p b) =
     a ^ p * (↑p * mydelta g p b) +  b ^ p * (↑p *mydelta g p a) + (↑p * mydelta g p a )*(↑p * mydelta g p b):= by
     ring
    rw [this2]
    simp_rw [← mylem]
    simp_rw [mymap]
    rw [mul_sub,mul_sub,mul_sub,sub_mul,sub_mul]
    simp
    simp_rw [← mul_assoc]
    have this3 : (a ^ p * sum b fun n a => (a : ℤ[X]) * (X ^ p + (p : ℤ[X]) * g) ^ n) - a ^ p * b ^ p +
      ((b ^ p * sum a fun n a => (a : ℤ[X]) * (X ^ p + (p : ℤ[X]) * g) ^ n) - b ^ p * a ^ p) +
    ((((sum a fun n a => (a : ℤ[X]) * (X ^ p + (p : ℤ[X]) * g) ^ n) * sum b fun n a => (a : ℤ[X]) * (X ^ p + (p : ℤ[X]) * g) ^ n) -
        a ^ p * sum b fun n a => (a : ℤ[X]) * (X ^ p + (p : ℤ[X]) * g) ^ n) -
      ((sum a fun n a => (a : ℤ[X]) * (X ^ p + (p : ℤ[X]) * g) ^ n) * b ^ p - a ^ p * b ^ p)) = ((sum a fun n a => (a : ℤ[X]) * (X ^ p + (p : ℤ[X]) * g) ^ n) * sum b fun n a => (a : ℤ[X]) * (X ^ p + (p : ℤ[X]) * g) ^ n) - a ^ p * b ^ p := by
      ring
    rw [this3,mul_pow]
    congr
    rw [sum,sum,sum,mul_eq_sum_sum ]
    simp
    ring_nf

    sorry
  map_add := by
    sorry

end example3

-- ########### endo ###########
section endo

def delta_ring_endo {A : Type}[CommRing A](p : ℕ)(hp : (Nat.Prime p))(delta: A → A)[DeltaRing A p delta]  : A →+* A where
  toFun f := ((f^p) + p * delta (f))
  map_zero' := by
    simp_rw [ne_eq,Delta_zero p delta]
    rw [mul_zero, add_zero, zero_pow]
    exact Nat.Prime.pos hp

  map_one' := by
    simp_rw [one_pow, add_right_eq_self,Delta_one p delta,mul_zero]

  map_mul' := by
    intro x y
    simp_rw [Delta_mul x y p delta]
    ring

  map_add' := by
    intro x y
    simp_rw [Delta_add x y p delta,sub_eq_add_neg,mul_add,mul_neg,← sub_eq_add_neg]
    rw[Commute.add_pow_prime_eq hp]
    ring
    exact Commute.all x y


end endo

-- ########### mulprop ###########
section mulprop

lemma delta_ring_map_mul_other_form {A : Type}[CommRing A](x y : A)(p : ℕ)(hp : (Nat.Prime p))(delta: A → A)[DeltaRing A p delta] : delta (x*y) =
      ((delta_ring_endo p hp delta).toFun (x) * delta (y)) + (y^p * delta (x)) := by
  rw [Delta_mul x y p delta,RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
  simp_rw [add_left_inj,mul_comm (x^p),mul_assoc,delta_ring_endo,RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
  ring

end mulprop

-- ########### addprop ###########
section addprop

lemma a1  {A : Type}[CommRing A](x y : A)(p : ℕ)[Invertible (p : A)] : -(↑p * ∑ k in Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(Nat.choose p k / p)) * ⅟ (p : A)
 = -( ∑ k in Finset.Ioo 0 p, x ^ k * y ^ (p - k) * ↑(Nat.choose p k / p)) := by

   rw [mul_invOf_eq_iff_eq_mul_right]
   simp only [gt_iff_lt, not_lt, nonpos_iff_eq_zero, ge_iff_le, neg_mul, neg_inj]
   apply mul_comm


lemma delta_ring_map_add_other_form {A : Type}[CommRing A](x y : A)(p : ℕ)(hp : (Nat.Prime p))(delta: A → A)[DeltaRing A p delta][Invertible (p : A)] : delta (x+y) =
      delta (x) + delta (y) + ((x^p + y^p - (x+y)^p)*⅟ (p : A)) := by

  rw [Commute.add_pow_prime_eq hp,sub_eq_add_neg]
  simp_rw [gt_iff_lt, not_lt, nonpos_iff_eq_zero, ge_iff_le, Nat.isUnit_iff, neg_add_rev]
  rw [add_comm _ (-y^p+-x^p),← add_assoc (x^p + y^p),← neg_add_rev,← sub_eq_add_neg,add_right_neg,sub_eq_add_neg]
  rw [zero_add,a1 x y p,← sub_eq_add_neg,Delta_add x y p delta]
  exact Commute.all x y

end addprop

-- ########### unique ###########
section unique

lemma delta_is_unique {A : Type}[CommRing A](p : ℕ)(hp : Nat.Prime p)(ht: ∀x:A, p*x=0 ↔ x=0)(delta: A → A)[DeltaRing A p delta](delta2: A → A)[DeltaRing A p delta2] : delta_ring_endo p hp delta = delta_ring_endo p hp delta2 ↔ delta=delta2  := by
  apply Iff.intro
  intro h
  ext1 x
  simp_rw [delta_ring_endo,RingHom.mk.injEq, MonoidHom.mk.injEq, OneHom.mk.injEq] at h
  have jsak : x^p +p*delta x = x^p +p*delta2 x := by
   apply congrFun h x
  simp at jsak
  have jgdsL : p*(delta x - delta2 x) = 0:= by
    rw [mul_sub,jsak]
    ring
  rw [ht (delta x - delta2 x)] at jgdsL
  rw [← sub_eq_zero]
  exact jgdsL

  intro h2
  simp_rw [delta_ring_endo,RingHom.mk.injEq, MonoidHom.mk.injEq, OneHom.mk.injEq]
  rw [h2]

end unique

-- ########### delmap ###########
section delmap

lemma a2 {A : Type}[CommRing A]  (p : ℕ) (delta: A → A) [DeltaRing A p delta][Invertible (p : A)](hp : (Nat.Prime p))  : (delta_ring_endo p hp delta).toFun (⅟ (p : A)) = ⅟ (p : A) := by

  simp_rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
  refine Eq.symm (invOf_eq_right_inv ?hac)
  have  asd : (delta_ring_endo p hp delta).toFun ((p:A)) * (delta_ring_endo p hp delta).toFun (⅟ (p:A)) = (p:A) * (delta_ring_endo p hp delta).toFun (⅟ (p:A)) := by
    simp_rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe, map_natCast]
  simp_rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe] at asd
  rw [← asd,← map_mul]
  simp only [mul_invOf_self', map_one]

lemma delta_endo_form {A : Type}[CommRing A]  (p : ℕ) [Invertible (p : A)](delta: A → A) [DeltaRing A p delta](x:A) (hp : (Nat.Prime p)): delta (x) = ((delta_ring_endo p hp delta).toFun (x) - x^p)*⅟ (p : A) := by
  simp_rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
  rw [← mul_right_eq_iff_eq_mul_invOf]
  refine Iff.mpr eq_sub_iff_add_eq ?_
  rw [mul_comm,add_comm]
  rfl

lemma is_delta_map_p_inv {A : Type}[CommRing A](x: A)(p : ℕ)(hp : (Nat.Prime p))(delta: A → A)[DeltaRing A p delta]
  [Invertible (p : A)] : (delta_ring_endo p hp delta).toFun (delta (x)) = delta ((delta_ring_endo p hp delta).toFun (x)) := by

  rw [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
  symm
  rw [delta_endo_form p delta,RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe,← map_pow,← map_sub,← a2 p delta hp,RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe,
    MonoidHom.toOneHom_coe,MonoidHom.coe_coe,← map_mul,delta_endo_form p delta]
  simp only [map_mul, map_sub, map_pow, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    MonoidHom.coe_coe]
  exact hp

end delmap
