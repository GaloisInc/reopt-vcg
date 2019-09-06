def addpd1 : instruction :=
  definst "addpd" $ do
    pattern fun (v_2685 : reg (bv 128)) (v_2686 : reg (bv 128)) => do
      v_4647 <- getRegister v_2686;
      v_4650 <- getRegister v_2685;
      setRegister (lhs.of_reg v_2686) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4647 0 64) 53 11) (MInt2Float (extract v_4650 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4647 64 128) 53 11) (MInt2Float (extract v_4650 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2684 : Mem) (v_2681 : reg (bv 128)) => do
      v_8750 <- getRegister v_2681;
      v_8753 <- evaluateAddress v_2684;
      v_8754 <- load v_8753 16;
      setRegister (lhs.of_reg v_2681) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8750 0 64) 53 11) (MInt2Float (extract v_8754 0 64) 53 11)) 64) (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8750 64 128) 53 11) (MInt2Float (extract v_8754 64 128) 53 11)) 64));
      pure ()
    pat_end
