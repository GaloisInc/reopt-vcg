def addsubpd1 : instruction :=
  definst "addsubpd" $ do
    pattern fun (v_2747 : reg (bv 128)) (v_2748 : reg (bv 128)) => do
      v_4821 <- getRegister v_2748;
      v_4824 <- getRegister v_2747;
      setRegister (lhs.of_reg v_2748) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4821 0 64) 53 11) (MInt2Float (extract v_4824 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4821 64 128) 53 11) (MInt2Float (extract v_4824 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2746 : Mem) (v_2743 : reg (bv 128)) => do
      v_8847 <- getRegister v_2743;
      v_8850 <- evaluateAddress v_2746;
      v_8851 <- load v_8850 16;
      setRegister (lhs.of_reg v_2743) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8847 0 64) 53 11) (MInt2Float (extract v_8851 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8847 64 128) 53 11) (MInt2Float (extract v_8851 64 128) 53 11)) 64));
      pure ()
    pat_end
