def addsubpd1 : instruction :=
  definst "addsubpd" $ do
    pattern fun (v_2659 : reg (bv 128)) (v_2660 : reg (bv 128)) => do
      v_4948 <- getRegister v_2660;
      v_4951 <- getRegister v_2659;
      setRegister (lhs.of_reg v_2660) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4948 0 64) 53 11) (MInt2Float (extract v_4951 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4948 64 128) 53 11) (MInt2Float (extract v_4951 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2654 : Mem) (v_2655 : reg (bv 128)) => do
      v_9206 <- getRegister v_2655;
      v_9209 <- evaluateAddress v_2654;
      v_9210 <- load v_9209 16;
      setRegister (lhs.of_reg v_2655) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9206 0 64) 53 11) (MInt2Float (extract v_9210 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9206 64 128) 53 11) (MInt2Float (extract v_9210 64 128) 53 11)) 64));
      pure ()
    pat_end
