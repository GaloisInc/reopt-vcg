def cvtsd2ss1 : instruction :=
  definst "cvtsd2ss" $ do
    pattern fun (v_2608 : reg (bv 128)) (v_2609 : reg (bv 128)) => do
      v_4205 <- getRegister v_2609;
      v_4207 <- getRegister v_2608;
      setRegister (lhs.of_reg v_2609) (concat (extract v_4205 0 96) (Float2MInt (roundFloat (MInt2Float (extract v_4207 64 128) 53 11) 24 8) 32));
      pure ()
    pat_end;
    pattern fun (v_2603 : Mem) (v_2604 : reg (bv 128)) => do
      v_7914 <- getRegister v_2604;
      v_7916 <- evaluateAddress v_2603;
      v_7917 <- load v_7916 8;
      setRegister (lhs.of_reg v_2604) (concat (extract v_7914 0 96) (Float2MInt (roundFloat (MInt2Float v_7917 53 11) 24 8) 32));
      pure ()
    pat_end
