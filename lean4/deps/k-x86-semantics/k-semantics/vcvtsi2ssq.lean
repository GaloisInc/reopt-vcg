def vcvtsi2ssq1 : instruction :=
  definst "vcvtsi2ssq" $ do
    pattern fun (v_3305 : reg (bv 64)) (v_3303 : reg (bv 128)) (v_3304 : reg (bv 128)) => do
      v_6203 <- getRegister v_3303;
      v_6205 <- getRegister v_3305;
      setRegister (lhs.of_reg v_3304) (concat (extract v_6203 0 96) (Float2MInt (Int2Float (svalueMInt v_6205) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3292 : Mem) (v_3293 : reg (bv 128)) (v_3294 : reg (bv 128)) => do
      v_10233 <- getRegister v_3293;
      v_10235 <- evaluateAddress v_3292;
      v_10236 <- load v_10235 8;
      setRegister (lhs.of_reg v_3294) (concat (extract v_10233 0 96) (Float2MInt (Int2Float (svalueMInt v_10236) 24 8) 32));
      pure ()
    pat_end
