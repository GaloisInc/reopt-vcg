def cvtps2pd1 : instruction :=
  definst "cvtps2pd" $ do
    pattern fun (v_2581 : reg (bv 128)) (v_2582 : reg (bv 128)) => do
      v_4174 <- getRegister v_2581;
      setRegister (lhs.of_reg v_2582) (concat (Float2MInt (roundFloat (MInt2Float (extract v_4174 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_4174 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2576 : Mem) (v_2577 : reg (bv 128)) => do
      v_7894 <- evaluateAddress v_2576;
      v_7895 <- load v_7894 8;
      setRegister (lhs.of_reg v_2577) (concat (Float2MInt (roundFloat (MInt2Float (extract v_7895 0 32) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_7895 32 64) 24 8) 53 11) 64));
      pure ()
    pat_end
