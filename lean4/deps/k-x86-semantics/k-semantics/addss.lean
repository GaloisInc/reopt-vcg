def addss1 : instruction :=
  definst "addss" $ do
    pattern fun (v_2738 : reg (bv 128)) (v_2739 : reg (bv 128)) => do
      v_4806 <- getRegister v_2739;
      v_4810 <- getRegister v_2738;
      setRegister (lhs.of_reg v_2739) (concat (extract v_4806 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4806 96 128) 24 8) (MInt2Float (extract v_4810 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2737 : Mem) (v_2734 : reg (bv 128)) => do
      v_8836 <- getRegister v_2734;
      v_8840 <- evaluateAddress v_2737;
      v_8841 <- load v_8840 4;
      setRegister (lhs.of_reg v_2734) (concat (extract v_8836 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8836 96 128) 24 8) (MInt2Float v_8841 24 8)) 32));
      pure ()
    pat_end
