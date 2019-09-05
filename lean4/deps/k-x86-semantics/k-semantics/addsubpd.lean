def addsubpd1 : instruction :=
  definst "addsubpd" $ do
    pattern fun (v_2723 : reg (bv 128)) (v_2724 : reg (bv 128)) => do
      v_4930 <- getRegister v_2724;
      v_4933 <- getRegister v_2723;
      setRegister (lhs.of_reg v_2724) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4930 0 64) 53 11) (MInt2Float (extract v_4933 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4930 64 128) 53 11) (MInt2Float (extract v_4933 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_2718 : Mem) (v_2719 : reg (bv 128)) => do
      v_9018 <- getRegister v_2719;
      v_9021 <- evaluateAddress v_2718;
      v_9022 <- load v_9021 16;
      setRegister (lhs.of_reg v_2719) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_9018 0 64) 53 11) (MInt2Float (extract v_9022 0 64) 53 11)) 64) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_9018 64 128) 53 11) (MInt2Float (extract v_9022 64 128) 53 11)) 64));
      pure ()
    pat_end
