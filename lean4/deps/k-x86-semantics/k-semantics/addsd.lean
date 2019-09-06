def addsd1 : instruction :=
  definst "addsd" $ do
    pattern fun (v_2729 : reg (bv 128)) (v_2730 : reg (bv 128)) => do
      v_4791 <- getRegister v_2730;
      v_4795 <- getRegister v_2729;
      setRegister (lhs.of_reg v_2730) (concat (extract v_4791 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4791 64 128) 53 11) (MInt2Float (extract v_4795 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2728 : Mem) (v_2725 : reg (bv 128)) => do
      v_8825 <- getRegister v_2725;
      v_8829 <- evaluateAddress v_2728;
      v_8830 <- load v_8829 8;
      setRegister (lhs.of_reg v_2725) (concat (extract v_8825 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8825 64 128) 53 11) (MInt2Float v_8830 53 11)) 64));
      pure ()
    pat_end
