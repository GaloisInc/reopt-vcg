def hsubpd1 : instruction :=
  definst "hsubpd" $ do
    pattern fun (v_2923 : reg (bv 128)) (v_2924 : reg (bv 128)) => do
      v_4843 <- getRegister v_2923;
      v_4850 <- getRegister v_2924;
      setRegister (lhs.of_reg v_2924) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4843 64 128) 53 11) (MInt2Float (extract v_4843 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4850 64 128) 53 11) (MInt2Float (extract v_4850 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2919 : Mem) (v_2920 : reg (bv 128)) => do
      v_8307 <- evaluateAddress v_2919;
      v_8308 <- load v_8307 16;
      v_8315 <- getRegister v_2920;
      setRegister (lhs.of_reg v_2920) (concat (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8308 64 128) 53 11) (MInt2Float (extract v_8308 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8315 64 128) 53 11) (MInt2Float (extract v_8315 0 64) 53 11)) 64));
      pure ()
    pat_end
