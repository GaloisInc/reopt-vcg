def cvtsd2ss1 : instruction :=
  definst "cvtsd2ss" $ do
    pattern fun (v_2634 : reg (bv 128)) (v_2635 : reg (bv 128)) => do
      v_4226 <- getRegister v_2635;
      v_4228 <- getRegister v_2634;
      setRegister (lhs.of_reg v_2635) (concat (extract v_4226 0 96) (Float2MInt (roundFloat (MInt2Float (extract v_4228 64 128) 53 11) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2630 : Mem) (v_2631 : reg (bv 128)) => do
      v_7924 <- getRegister v_2631;
      v_7926 <- evaluateAddress v_2630;
      v_7927 <- load v_7926 8;
      setRegister (lhs.of_reg v_2631) (concat (extract v_7924 0 96) (Float2MInt (roundFloat (MInt2Float v_7927 53 11) 24 8) 32));
      pure ()
    pat_end
