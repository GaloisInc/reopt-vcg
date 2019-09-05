def vrcpps1 : instruction :=
  definst "vrcpps" $ do
    pattern fun (v_2841 : reg (bv 128)) (v_2842 : reg (bv 128)) => do
      v_6558 <- getRegister v_2841;
      setRegister (lhs.of_reg v_2842) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6558 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6558 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6558 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6558 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2850 : reg (bv 256)) (v_2851 : reg (bv 256)) => do
      v_6583 <- getRegister v_2850;
      setRegister (lhs.of_reg v_2851) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6583 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6583 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6583 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6583 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6583 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6583 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6583 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6583 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2836 : Mem) (v_2837 : reg (bv 128)) => do
      v_12577 <- evaluateAddress v_2836;
      v_12578 <- load v_12577 16;
      setRegister (lhs.of_reg v_2837) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12578 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12578 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12578 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12578 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2845 : Mem) (v_2846 : reg (bv 256)) => do
      v_12599 <- evaluateAddress v_2845;
      v_12600 <- load v_12599 32;
      setRegister (lhs.of_reg v_2846) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12600 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12600 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12600 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12600 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12600 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12600 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12600 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12600 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
