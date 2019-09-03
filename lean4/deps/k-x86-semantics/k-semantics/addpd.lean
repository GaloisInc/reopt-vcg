def addpd1 : instruction :=
  definst "addpd" $ do
    pattern fun (v_2597 : reg (bv 128)) (v_2598 : reg (bv 128)) => do
      v_4750 <- getRegister v_2598;
      v_4753 <- getRegister v_2597;
      setRegister (lhs.of_reg v_2598) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4750 0 64) 53 11) (MInt2Float (extract v_4753 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4750 64 128) 53 11) (MInt2Float (extract v_4753 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2592 : Mem) (v_2593 : reg (bv 128)) => do
      v_9101 <- getRegister v_2593;
      v_9104 <- evaluateAddress v_2592;
      v_9105 <- load v_9104 16;
      setRegister (lhs.of_reg v_2593) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9101 0 64) 53 11) (MInt2Float (extract v_9105 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9101 64 128) 53 11) (MInt2Float (extract v_9105 64 128) 53 11)) 64));
      pure ()
    pat_end
