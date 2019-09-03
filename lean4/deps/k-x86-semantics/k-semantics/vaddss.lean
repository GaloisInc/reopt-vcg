def vaddss1 : instruction :=
  definst "vaddss" $ do
    pattern fun (v_2638 : reg (bv 128)) (v_2639 : reg (bv 128)) (v_2640 : reg (bv 128)) => do
      v_5222 <- getRegister v_2639;
      v_5224 <- eval (extract v_5222 96 128);
      v_5232 <- getRegister v_2638;
      v_5233 <- eval (extract v_5232 96 128);
      setRegister (lhs.of_reg v_2640) (concat (extract v_5222 0 96) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5224 0 1)) (uvalueMInt (extract v_5224 1 9)) (uvalueMInt (extract v_5224 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_5233 0 1)) (uvalueMInt (extract v_5233 1 9)) (uvalueMInt (extract v_5233 9 32)))) 32));
      pure ()
    pat_end;
    pattern fun (v_2630 : Mem) (v_2633 : reg (bv 128)) (v_2634 : reg (bv 128)) => do
      v_10753 <- getRegister v_2633;
      v_10755 <- eval (extract v_10753 96 128);
      v_10763 <- evaluateAddress v_2630;
      v_10764 <- load v_10763 4;
      setRegister (lhs.of_reg v_2634) (concat (extract v_10753 0 96) (Float2MInt (_+Float__FLOAT (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10755 0 1)) (uvalueMInt (extract v_10755 1 9)) (uvalueMInt (extract v_10755 9 32))) (MIntToFloatImpl 24 8 (uvalueMInt (extract v_10764 0 1)) (uvalueMInt (extract v_10764 1 9)) (uvalueMInt (extract v_10764 9 32)))) 32));
      pure ()
    pat_end
