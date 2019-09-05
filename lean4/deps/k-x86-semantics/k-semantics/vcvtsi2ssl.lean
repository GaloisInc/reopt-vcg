def vcvtsi2ssl1 : instruction :=
  definst "vcvtsi2ssl" $ do
    pattern fun (v_3289 : reg (bv 32)) (v_3287 : reg (bv 128)) (v_3288 : reg (bv 128)) => do
      v_6189 <- getRegister v_3287;
      v_6191 <- getRegister v_3289;
      setRegister (lhs.of_reg v_3288) (concat (extract v_6189 0 96) (Float2MInt (Int2Float (svalueMInt v_6191) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_3276 : Mem) (v_3277 : reg (bv 128)) (v_3278 : reg (bv 128)) => do
      v_10224 <- getRegister v_3277;
      v_10226 <- evaluateAddress v_3276;
      v_10227 <- load v_10226 4;
      setRegister (lhs.of_reg v_3278) (concat (extract v_10224 0 96) (Float2MInt (Int2Float (svalueMInt v_10227) 24 8) 32));
      pure ()
    pat_end
