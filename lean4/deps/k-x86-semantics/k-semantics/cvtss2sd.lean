def cvtss2sd1 : instruction :=
  definst "cvtss2sd" $ do
    pattern fun (v_2679 : reg (bv 128)) (v_2680 : reg (bv 128)) => do
      v_4287 <- getRegister v_2680;
      v_4289 <- getRegister v_2679;
      setRegister (lhs.of_reg v_2680) (concat (extract v_4287 0 64) (Float2MInt (roundFloat (MInt2Float (extract v_4289 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2675 : Mem) (v_2676 : reg (bv 128)) => do
      v_7969 <- getRegister v_2676;
      v_7971 <- evaluateAddress v_2675;
      v_7972 <- load v_7971 4;
      setRegister (lhs.of_reg v_2676) (concat (extract v_7969 0 64) (Float2MInt (roundFloat (MInt2Float v_7972 24 8) 53 11) 64));
      pure ()
    pat_end
