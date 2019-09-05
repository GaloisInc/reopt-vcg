def vrcpss1 : instruction :=
  definst "vrcpss" $ do
    pattern fun (v_2860 : reg (bv 128)) (v_2861 : reg (bv 128)) (v_2862 : reg (bv 128)) => do
      v_6629 <- getRegister v_2861;
      v_6631 <- getRegister v_2860;
      setRegister (lhs.of_reg v_2862) (concat (extract v_6629 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6631 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2854 : Mem) (v_2855 : reg (bv 128)) (v_2856 : reg (bv 128)) => do
      v_12641 <- getRegister v_2855;
      v_12643 <- evaluateAddress v_2854;
      v_12644 <- load v_12643 4;
      setRegister (lhs.of_reg v_2856) (concat (extract v_12641 0 96) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float v_12644 24 8)) 32));
      pure ()
    pat_end
