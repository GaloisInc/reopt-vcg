def vdivss1 : instruction :=
  definst "vdivss" $ do
    pattern fun (v_3402 : reg (bv 128)) (v_3403 : reg (bv 128)) (v_3404 : reg (bv 128)) => do
      v_6597 <- getRegister v_3403;
      v_6601 <- getRegister v_3402;
      setRegister (lhs.of_reg v_3404) (concat (extract v_6597 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6597 96 128) 24 8) (MInt2Float (extract v_6601 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_3394 : Mem) (v_3397 : reg (bv 128)) (v_3398 : reg (bv 128)) => do
      v_10748 <- getRegister v_3397;
      v_10752 <- evaluateAddress v_3394;
      v_10753 <- load v_10752 4;
      setRegister (lhs.of_reg v_3398) (concat (extract v_10748 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10748 96 128) 24 8) (MInt2Float v_10753 24 8)) 32));
      pure ()
    pat_end
