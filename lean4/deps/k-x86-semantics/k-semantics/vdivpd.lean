def vdivpd1 : instruction :=
  definst "vdivpd" $ do
    pattern fun (v_3438 : reg (bv 128)) (v_3439 : reg (bv 128)) (v_3440 : reg (bv 128)) => do
      v_6376 <- getRegister v_3439;
      v_6379 <- getRegister v_3438;
      setRegister (lhs.of_reg v_3440) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6376 0 64) 53 11) (MInt2Float (extract v_6379 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6376 64 128) 53 11) (MInt2Float (extract v_6379 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3446 : reg (bv 256)) (v_3447 : reg (bv 256)) (v_3448 : reg (bv 256)) => do
      v_6397 <- getRegister v_3447;
      v_6400 <- getRegister v_3446;
      setRegister (lhs.of_reg v_3448) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6397 0 64) 53 11) (MInt2Float (extract v_6400 0 64) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6397 64 128) 53 11) (MInt2Float (extract v_6400 64 128) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6397 128 192) 53 11) (MInt2Float (extract v_6400 128 192) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6397 192 256) 53 11) (MInt2Float (extract v_6400 192 256) 53 11)) 64))));
      pure ()
    pat_end;
    pattern fun (v_3430 : Mem) (v_3433 : reg (bv 128)) (v_3434 : reg (bv 128)) => do
      v_10388 <- getRegister v_3433;
      v_10391 <- evaluateAddress v_3430;
      v_10392 <- load v_10391 16;
      setRegister (lhs.of_reg v_3434) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10388 0 64) 53 11) (MInt2Float (extract v_10392 0 64) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10388 64 128) 53 11) (MInt2Float (extract v_10392 64 128) 53 11)) 64));
      pure ()
    pat_end;
    pattern fun (v_3441 : Mem) (v_3442 : reg (bv 256)) (v_3443 : reg (bv 256)) => do
      v_10405 <- getRegister v_3442;
      v_10408 <- evaluateAddress v_3441;
      v_10409 <- load v_10408 32;
      setRegister (lhs.of_reg v_3443) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10405 0 64) 53 11) (MInt2Float (extract v_10409 0 64) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10405 64 128) 53 11) (MInt2Float (extract v_10409 64 128) 53 11)) 64) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10405 128 192) 53 11) (MInt2Float (extract v_10409 128 192) 53 11)) 64) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10405 192 256) 53 11) (MInt2Float (extract v_10409 192 256) 53 11)) 64))));
      pure ()
    pat_end
