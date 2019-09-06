def addsubps1 : instruction :=
  definst "addsubps" $ do
    pattern fun (v_2756 : reg (bv 128)) (v_2757 : reg (bv 128)) => do
      v_4841 <- getRegister v_2757;
      v_4844 <- getRegister v_2756;
      setRegister (lhs.of_reg v_2757) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4841 0 32) 24 8) (MInt2Float (extract v_4844 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4841 32 64) 24 8) (MInt2Float (extract v_4844 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_4841 64 96) 24 8) (MInt2Float (extract v_4844 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_4841 96 128) 24 8) (MInt2Float (extract v_4844 96 128) 24 8)) 32)));
      pure ()
    pat_end;
    pattern fun (v_2755 : Mem) (v_2752 : reg (bv 128)) => do
      v_8864 <- getRegister v_2752;
      v_8867 <- evaluateAddress v_2755;
      v_8868 <- load v_8867 16;
      setRegister (lhs.of_reg v_2752) (concat (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8864 0 32) 24 8) (MInt2Float (extract v_8868 0 32) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8864 32 64) 24 8) (MInt2Float (extract v_8868 32 64) 24 8)) 32)) (concat (Float2MInt (_+Float__FLOAT (MInt2Float (extract v_8864 64 96) 24 8) (MInt2Float (extract v_8868 64 96) 24 8)) 32) (Float2MInt (_-Float__FLOAT (MInt2Float (extract v_8864 96 128) 24 8) (MInt2Float (extract v_8868 96 128) 24 8)) 32)));
      pure ()
    pat_end
