def subsd1 : instruction :=
  definst "subsd" $ do
    pattern fun (v_3286 : reg (bv 128)) (v_3287 : reg (bv 128)) => do
      v_6618 <- getRegister v_3287;
      v_6622 <- getRegister v_3286;
      setRegister (lhs.of_reg v_3287) (concat (extract v_6618 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_6618 64 128) 53 11) (MInt2Float (extract v_6622 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3283 : Mem) (v_3282 : reg (bv 128)) => do
      v_9373 <- getRegister v_3282;
      v_9377 <- evaluateAddress v_3283;
      v_9378 <- load v_9377 8;
      setRegister (lhs.of_reg v_3282) (concat (extract v_9373 0 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9373 64 128) 53 11) (MInt2Float v_9378 53 11)) 64));
      pure ()
    pat_end
