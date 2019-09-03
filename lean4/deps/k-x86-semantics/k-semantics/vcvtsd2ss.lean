def vcvtsd2ss1 : instruction :=
  definst "vcvtsd2ss" $ do
    pattern fun (v_3178 : reg (bv 128)) (v_3179 : reg (bv 128)) (v_3180 : reg (bv 128)) => do
      v_6891 <- getRegister v_3179;
      v_6893 <- getRegister v_3178;
      v_6894 <- eval (extract v_6893 64 128);
      setRegister (lhs.of_reg v_3180) (concat (extract v_6891 0 96) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_6894 0 1)) (uvalueMInt (extract v_6894 1 12)) (uvalueMInt (extract v_6894 12 64))) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3170 : Mem) (v_3173 : reg (bv 128)) (v_3174 : reg (bv 128)) => do
      v_12155 <- getRegister v_3173;
      v_12157 <- evaluateAddress v_3170;
      v_12158 <- load v_12157 8;
      setRegister (lhs.of_reg v_3174) (concat (extract v_12155 0 96) (Float2MInt (roundFloat (MIntToFloatImpl 53 11 (uvalueMInt (extract v_12158 0 1)) (uvalueMInt (extract v_12158 1 12)) (uvalueMInt (extract v_12158 12 64))) 24 8) 32));
      pure ()
    pat_end
