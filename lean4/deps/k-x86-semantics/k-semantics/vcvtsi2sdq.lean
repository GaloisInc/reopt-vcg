def vcvtsi2sdq1 : instruction :=
  definst "vcvtsi2sdq" $ do
    pattern fun (v_3212 : reg (bv 64)) (v_3216 : reg (bv 128)) (v_3217 : reg (bv 128)) => do
      v_6930 <- getRegister v_3216;
      v_6932 <- getRegister v_3212;
      setRegister (lhs.of_reg v_3217) (concat (extract v_6930 0 64) (Float2MInt (Int2Float (svalueMInt v_6932) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_3202 : Mem) (v_3205 : reg (bv 128)) (v_3206 : reg (bv 128)) => do
      v_12180 <- getRegister v_3205;
      v_12182 <- evaluateAddress v_3202;
      v_12183 <- load v_12182 8;
      setRegister (lhs.of_reg v_3206) (concat (extract v_12180 0 64) (Float2MInt (Int2Float (svalueMInt v_12183) 53 11) 64));
      pure ()
    pat_end
