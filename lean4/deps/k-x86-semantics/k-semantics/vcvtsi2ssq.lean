def vcvtsi2ssq1 : instruction :=
  definst "vcvtsi2ssq" $ do
    pattern fun (v_3249 : reg (bv 64)) (v_3253 : reg (bv 128)) (v_3254 : reg (bv 128)) => do
      v_6962 <- getRegister v_3253;
      v_6964 <- getRegister v_3249;
      setRegister (lhs.of_reg v_3254) (concat (extract v_6962 0 96) (Float2MInt (Int2Float (svalueMInt v_6964) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3239 : Mem) (v_3242 : reg (bv 128)) (v_3243 : reg (bv 128)) => do
      v_12199 <- getRegister v_3242;
      v_12201 <- evaluateAddress v_3239;
      v_12202 <- load v_12201 8;
      setRegister (lhs.of_reg v_3243) (concat (extract v_12199 0 96) (Float2MInt (Int2Float (svalueMInt v_12202) 24 8) 32));
      pure ()
    pat_end
