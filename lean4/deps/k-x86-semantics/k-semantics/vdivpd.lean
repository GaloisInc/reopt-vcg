def vdivpd1 : instruction :=
  definst "vdivpd" $ do
    pattern fun (v_3411 : reg (bv 128)) (v_3412 : reg (bv 128)) (v_3413 : reg (bv 128)) => do
      v_6349 <- getRegister v_3412;
      v_6352 <- getRegister v_3411;
      setRegister (lhs.of_reg v_3413) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6349 0 64) 53 11) (MInt2Float (extract v_6352 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6349 64 128) 53 11) (MInt2Float (extract v_6352 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3421 : reg (bv 256)) (v_3422 : reg (bv 256)) (v_3423 : reg (bv 256)) => do
      v_6370 <- getRegister v_3422;
      v_6373 <- getRegister v_3421;
      setRegister (lhs.of_reg v_3423) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6370 0 64) 53 11) (MInt2Float (extract v_6373 0 64) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6370 64 128) 53 11) (MInt2Float (extract v_6373 64 128) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6370 128 192) 53 11) (MInt2Float (extract v_6373 128 192) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6370 192 256) 53 11) (MInt2Float (extract v_6373 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3405 : Mem) (v_3406 : reg (bv 128)) (v_3407 : reg (bv 128)) => do
      v_10361 <- getRegister v_3406;
      v_10364 <- evaluateAddress v_3405;
      v_10365 <- load v_10364 16;
      setRegister (lhs.of_reg v_3407) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10361 0 64) 53 11) (MInt2Float (extract v_10365 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10361 64 128) 53 11) (MInt2Float (extract v_10365 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3416 : Mem) (v_3417 : reg (bv 256)) (v_3418 : reg (bv 256)) => do
      v_10378 <- getRegister v_3417;
      v_10381 <- evaluateAddress v_3416;
      v_10382 <- load v_10381 32;
      setRegister (lhs.of_reg v_3418) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10378 0 64) 53 11) (MInt2Float (extract v_10382 0 64) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10378 64 128) 53 11) (MInt2Float (extract v_10382 64 128) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10378 128 192) 53 11) (MInt2Float (extract v_10382 128 192) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10378 192 256) 53 11) (MInt2Float (extract v_10382 192 256) 53 11)) 64))));
      pure ()
    pat_end
