def vrcpps1 : instruction :=
  definst "vrcpps" $ do
    pattern fun (v_2868 : reg (bv 128)) (v_2869 : reg (bv 128)) => do
      v_6585 <- getRegister v_2868;
      setRegister (lhs.of_reg v_2869) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6585 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6585 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6585 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6585 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2877 : reg (bv 256)) (v_2878 : reg (bv 256)) => do
      v_6610 <- getRegister v_2877;
      setRegister (lhs.of_reg v_2878) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6610 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6610 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6610 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6610 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6610 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6610 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6610 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_6610 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_2863 : Mem) (v_2864 : reg (bv 128)) => do
      v_12604 <- evaluateAddress v_2863;
      v_12605 <- load v_12604 16;
      setRegister (lhs.of_reg v_2864) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12605 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12605 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12605 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12605 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_2872 : Mem) (v_2873 : reg (bv 256)) => do
      v_12626 <- evaluateAddress v_2872;
      v_12627 <- load v_12626 32;
      setRegister (lhs.of_reg v_2873) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12627 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12627 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12627 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12627 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12627 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12627 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12627 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT 1e+00 (MInt2Float (extract v_12627 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
