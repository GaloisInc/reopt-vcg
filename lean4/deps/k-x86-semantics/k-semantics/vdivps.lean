def vdivps1 : instruction :=
  definst "vdivps" $ do
    pattern fun (v_3369 : reg (bv 128)) (v_3370 : reg (bv 128)) (v_3371 : reg (bv 128)) => do
      v_6483 <- getRegister v_3370;
      v_6486 <- getRegister v_3369;
      setRegister (lhs.of_reg v_3371) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6483 0 32) 24 8) (MInt2Float (extract v_6486 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6483 32 64) 24 8) (MInt2Float (extract v_6486 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6483 64 96) 24 8) (MInt2Float (extract v_6486 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6483 96 128) 24 8) (MInt2Float (extract v_6486 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3378 : reg (bv 256)) (v_3379 : reg (bv 256)) (v_3380 : reg (bv 256)) => do
      v_6518 <- getRegister v_3379;
      v_6521 <- getRegister v_3378;
      setRegister (lhs.of_reg v_3380) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6518 0 32) 24 8) (MInt2Float (extract v_6521 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6518 32 64) 24 8) (MInt2Float (extract v_6521 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6518 64 96) 24 8) (MInt2Float (extract v_6521 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6518 96 128) 24 8) (MInt2Float (extract v_6521 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6518 128 160) 24 8) (MInt2Float (extract v_6521 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6518 160 192) 24 8) (MInt2Float (extract v_6521 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6518 192 224) 24 8) (MInt2Float (extract v_6521 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6518 224 256) 24 8) (MInt2Float (extract v_6521 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3361 : Mem) (v_3364 : reg (bv 128)) (v_3365 : reg (bv 128)) => do
      v_10647 <- getRegister v_3364;
      v_10650 <- evaluateAddress v_3361;
      v_10651 <- load v_10650 16;
      setRegister (lhs.of_reg v_3365) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10647 0 32) 24 8) (MInt2Float (extract v_10651 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10647 32 64) 24 8) (MInt2Float (extract v_10651 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10647 64 96) 24 8) (MInt2Float (extract v_10651 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10647 96 128) 24 8) (MInt2Float (extract v_10651 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3372 : Mem) (v_3373 : reg (bv 256)) (v_3374 : reg (bv 256)) => do
      v_10678 <- getRegister v_3373;
      v_10681 <- evaluateAddress v_3372;
      v_10682 <- load v_10681 32;
      setRegister (lhs.of_reg v_3374) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10678 0 32) 24 8) (MInt2Float (extract v_10682 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10678 32 64) 24 8) (MInt2Float (extract v_10682 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10678 64 96) 24 8) (MInt2Float (extract v_10682 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10678 96 128) 24 8) (MInt2Float (extract v_10682 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10678 128 160) 24 8) (MInt2Float (extract v_10682 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10678 160 192) 24 8) (MInt2Float (extract v_10682 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10678 192 224) 24 8) (MInt2Float (extract v_10682 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10678 224 256) 24 8) (MInt2Float (extract v_10682 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
