def cvtps2pd1 : instruction :=
  definst "cvtps2pd" $ do
    pattern fun (v_2607 : reg (bv 128)) (v_2608 : reg (bv 128)) => do
      v_4195 <- getRegister v_2607;
      setRegister (lhs.of_reg v_2608) (concat (Float2MInt (roundFloat (MInt2Float (extract v_4195 64 96) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_4195 96 128) 24 8) 53 11) 64));
      pure ()
    pat_end;
    pattern fun (v_2603 : Mem) (v_2604 : reg (bv 128)) => do
      v_7904 <- evaluateAddress v_2603;
      v_7905 <- load v_7904 8;
      setRegister (lhs.of_reg v_2604) (concat (Float2MInt (roundFloat (MInt2Float (extract v_7905 0 32) 24 8) 53 11) 64) (Float2MInt (roundFloat (MInt2Float (extract v_7905 32 64) 24 8) 53 11) 64));
      pure ()
    pat_end
