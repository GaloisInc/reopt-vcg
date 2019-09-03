def vdivpd1 : instruction :=
  definst "vdivpd" $ do
    pattern fun (v_3347 : reg (bv 128)) (v_3348 : reg (bv 128)) (v_3349 : reg (bv 128)) => do
      v_6427 <- getRegister v_3348;
      v_6430 <- getRegister v_3347;
      setRegister (lhs.of_reg v_3349) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6427 0 64) 53 11) (MInt2Float (extract v_6430 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6427 64 128) 53 11) (MInt2Float (extract v_6430 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3356 : reg (bv 256)) (v_3357 : reg (bv 256)) (v_3358 : reg (bv 256)) => do
      v_6448 <- getRegister v_3357;
      v_6451 <- getRegister v_3356;
      setRegister (lhs.of_reg v_3358) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6448 0 64) 53 11) (MInt2Float (extract v_6451 0 64) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6448 64 128) 53 11) (MInt2Float (extract v_6451 64 128) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6448 128 192) 53 11) (MInt2Float (extract v_6451 128 192) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6448 192 256) 53 11) (MInt2Float (extract v_6451 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3339 : Mem) (v_3342 : reg (bv 128)) (v_3343 : reg (bv 128)) => do
      v_10599 <- getRegister v_3342;
      v_10602 <- evaluateAddress v_3339;
      v_10603 <- load v_10602 16;
      setRegister (lhs.of_reg v_3343) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10599 0 64) 53 11) (MInt2Float (extract v_10603 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10599 64 128) 53 11) (MInt2Float (extract v_10603 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3350 : Mem) (v_3351 : reg (bv 256)) (v_3352 : reg (bv 256)) => do
      v_10616 <- getRegister v_3351;
      v_10619 <- evaluateAddress v_3350;
      v_10620 <- load v_10619 32;
      setRegister (lhs.of_reg v_3352) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10616 0 64) 53 11) (MInt2Float (extract v_10620 0 64) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10616 64 128) 53 11) (MInt2Float (extract v_10620 64 128) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10616 128 192) 53 11) (MInt2Float (extract v_10620 128 192) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10616 192 256) 53 11) (MInt2Float (extract v_10620 192 256) 53 11)) 64))));
      pure ()
    pat_end
