def addss1 : instruction :=
  definst "addss" $ do
    pattern fun (v_2714 : reg (bv 128)) (v_2715 : reg (bv 128)) => do
      v_4915 <- getRegister v_2715;
      v_4919 <- getRegister v_2714;
      setRegister (lhs.of_reg v_2715) (concat (extract v_4915 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4915 96 128) 24 8) (MInt2Float (extract v_4919 96 128) 24 8)) 32));
      pure ()
    pat_end;
    pattern fun (v_2709 : Mem) (v_2710 : reg (bv 128)) => do
      v_9007 <- getRegister v_2710;
      v_9011 <- evaluateAddress v_2709;
      v_9012 <- load v_9011 4;
      setRegister (lhs.of_reg v_2710) (concat (extract v_9007 0 96) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9007 96 128) 24 8) (MInt2Float v_9012 24 8)) 32));
      pure ()
    pat_end
