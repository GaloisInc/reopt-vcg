def cvtsi2sdq1 : instruction :=
  definst "cvtsi2sdq" $ do
    pattern fun (v_2561 : reg (bv 64)) (v_2562 : reg (bv 128)) => do
      v_4220 <- getRegister v_2562;
      v_4222 <- getRegister v_2561;
      setRegister (lhs.of_reg v_2562) (concat (extract v_4220 0 64) (Float2MInt (Int2Float (svalueMInt v_4222) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2557 : Mem) (v_2558 : reg (bv 128)) => do
      v_8154 <- getRegister v_2558;
      v_8156 <- evaluateAddress v_2557;
      v_8157 <- load v_8156 8;
      setRegister (lhs.of_reg v_2558) (concat (extract v_8154 0 64) (Float2MInt (Int2Float (svalueMInt v_8157) 53 11) 64));
      pure ()
    pat_end
