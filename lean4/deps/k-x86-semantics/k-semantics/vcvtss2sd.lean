def vcvtss2sd1 : instruction :=
  definst "vcvtss2sd" $ do
    pattern fun (v_3263 : reg (bv 128)) (v_3264 : reg (bv 128)) (v_3265 : reg (bv 128)) => do
      v_6975 <- getRegister v_3264;
      v_6977 <- getRegister v_3263;
      v_6978 <- eval (extract v_6977 96 128);
      setRegister (lhs.of_reg v_3265) (concat (extract v_6975 0 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_6978 0 1)) (uvalueMInt (extract v_6978 1 9)) (uvalueMInt (extract v_6978 9 32))) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3255 : Mem) (v_3258 : reg (bv 128)) (v_3259 : reg (bv 128)) => do
      v_12208 <- getRegister v_3258;
      v_12210 <- evaluateAddress v_3255;
      v_12211 <- load v_12210 4;
      setRegister (lhs.of_reg v_3259) (concat (extract v_12208 0 64) (Float2MInt (roundFloat (MIntToFloatImpl 24 8 (uvalueMInt (extract v_12211 0 1)) (uvalueMInt (extract v_12211 1 9)) (uvalueMInt (extract v_12211 9 32))) 53 11) 64));
      pure ()
    pat_end
