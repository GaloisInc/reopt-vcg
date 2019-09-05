def addpd1 : instruction :=
  definst "addpd" $ do
    pattern fun (v_2661 : reg (bv 128)) (v_2662 : reg (bv 128)) => do
      v_4741 <- getRegister v_2662;
      v_4744 <- getRegister v_2661;
      setRegister (lhs.of_reg v_2662) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4741 0 64) 53 11) (MInt2Float (extract v_4744 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4741 64 128) 53 11) (MInt2Float (extract v_4744 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2656 : Mem) (v_2657 : reg (bv 128)) => do
      v_8916 <- getRegister v_2657;
      v_8919 <- evaluateAddress v_2656;
      v_8920 <- load v_8919 16;
      setRegister (lhs.of_reg v_2657) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8916 0 64) 53 11) (MInt2Float (extract v_8920 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8916 64 128) 53 11) (MInt2Float (extract v_8920 64 128) 53 11)) 64));
      pure ()
    pat_end
