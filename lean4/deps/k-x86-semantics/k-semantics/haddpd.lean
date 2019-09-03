def haddpd1 : instruction :=
  definst "haddpd" $ do
    pattern fun (v_2814 : reg (bv 128)) (v_2815 : reg (bv 128)) => do
      v_4791 <- getRegister v_2814;
      v_4798 <- getRegister v_2815;
      setRegister (lhs.of_reg v_2815) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4791 64 128) 53 11) (MInt2Float (extract v_4791 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4798 64 128) 53 11) (MInt2Float (extract v_4798 0 64) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2810 : Mem) (v_2811 : reg (bv 128)) => do
      v_8483 <- evaluateAddress v_2810;
      v_8484 <- load v_8483 16;
      v_8491 <- getRegister v_2811;
      setRegister (lhs.of_reg v_2811) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8484 64 128) 53 11) (MInt2Float (extract v_8484 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8491 64 128) 53 11) (MInt2Float (extract v_8491 0 64) 53 11)) 64));
      pure ()
    pat_end
