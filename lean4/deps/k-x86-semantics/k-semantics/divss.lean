def divss1 : instruction :=
  definst "divss" $ do
    pattern fun (v_2759 : reg (bv 128)) (v_2760 : reg (bv 128)) => do
      v_4615 <- getRegister v_2760;
      v_4619 <- getRegister v_2759;
      setRegister (lhs.of_reg v_2760) (concat (extract v_4615 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_4615 96 128) 24 8) (MInt2Float (extract v_4619 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2755 : Mem) (v_2756 : reg (bv 128)) => do
      v_8348 <- getRegister v_2756;
      v_8352 <- evaluateAddress v_2755;
      v_8353 <- load v_8352 4;
      setRegister (lhs.of_reg v_2756) (concat (extract v_8348 0 96) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_8348 96 128) 24 8) (MInt2Float v_8353 24 8)) 32));
      pure ()
    pat_end
