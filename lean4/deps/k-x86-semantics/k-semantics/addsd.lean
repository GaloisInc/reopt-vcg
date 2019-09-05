def addsd1 : instruction :=
  definst "addsd" $ do
    pattern fun (v_2705 : reg (bv 128)) (v_2706 : reg (bv 128)) => do
      v_4900 <- getRegister v_2706;
      v_4904 <- getRegister v_2705;
      setRegister (lhs.of_reg v_2706) (concat (extract v_4900 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4900 64 128) 53 11) (MInt2Float (extract v_4904 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2700 : Mem) (v_2701 : reg (bv 128)) => do
      v_8996 <- getRegister v_2701;
      v_9000 <- evaluateAddress v_2700;
      v_9001 <- load v_9000 8;
      setRegister (lhs.of_reg v_2701) (concat (extract v_8996 0 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8996 64 128) 53 11) (MInt2Float v_9001 53 11)) 64));
      pure ()
    pat_end
