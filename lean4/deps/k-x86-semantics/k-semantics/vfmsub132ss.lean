def vfmsub132ss1 : instruction :=
  definst "vfmsub132ss" $ do
    pattern fun (v_2816 : reg (bv 128)) (v_2817 : reg (bv 128)) (v_2818 : reg (bv 128)) => do
      v_7744 <- getRegister v_2818;
      v_7746 <- eval (extract v_7744 96 128);
      v_7754 <- getRegister v_2816;
      v_7755 <- eval (extract v_7754 96 128);
      v_7764 <- getRegister v_2817;
      v_7765 <- eval (extract v_7764 96 128);
      setRegister (lhs.of_reg v_2818) (concat (extract v_7744 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7746 0 1)) (uvalueMInt (extract v_7746 1 9)) (uvalueMInt (extract v_7746 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7755 0 1)) (uvalueMInt (extract v_7755 1 9)) (uvalueMInt (extract v_7755 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_7765 0 1)) (uvalueMInt (extract v_7765 1 9)) (uvalueMInt (extract v_7765 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2813 : Mem) (v_2811 : reg (bv 128)) (v_2812 : reg (bv 128)) => do
      v_18546 <- getRegister v_2812;
      v_18548 <- eval (extract v_18546 96 128);
      v_18556 <- evaluateAddress v_2813;
      v_18557 <- load v_18556 4;
      v_18566 <- getRegister v_2811;
      v_18567 <- eval (extract v_18566 96 128);
      setRegister (lhs.of_reg v_2812) (concat (extract v_18546 0 96) (Float2MInt (_-Float__FLOAT (_*Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18548 0 1)) (uvalueMInt (extract v_18548 1 9)) (uvalueMInt (extract v_18548 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18557 0 1)) (uvalueMInt (extract v_18557 1 9)) (uvalueMInt (extract v_18557 9 32)))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_18567 0 1)) (uvalueMInt (extract v_18567 1 9)) (uvalueMInt (extract v_18567 9 32)))) 32));
      pure ()
    pat_end
