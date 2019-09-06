def vdivps1 : instruction :=
  definst "vdivps" $ do
    pattern fun (v_3460 : reg (bv 128)) (v_3461 : reg (bv 128)) (v_3462 : reg (bv 128)) => do
      v_6432 <- getRegister v_3461;
      v_6435 <- getRegister v_3460;
      setRegister (lhs.of_reg v_3462) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6432 0 32) 24 8) (MInt2Float (extract v_6435 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6432 32 64) 24 8) (MInt2Float (extract v_6435 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6432 64 96) 24 8) (MInt2Float (extract v_6435 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6432 96 128) 24 8) (MInt2Float (extract v_6435 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3468 : reg (bv 256)) (v_3469 : reg (bv 256)) (v_3470 : reg (bv 256)) => do
      v_6467 <- getRegister v_3469;
      v_6470 <- getRegister v_3468;
      setRegister (lhs.of_reg v_3470) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6467 0 32) 24 8) (MInt2Float (extract v_6470 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6467 32 64) 24 8) (MInt2Float (extract v_6470 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6467 64 96) 24 8) (MInt2Float (extract v_6470 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6467 96 128) 24 8) (MInt2Float (extract v_6470 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6467 128 160) 24 8) (MInt2Float (extract v_6470 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6467 160 192) 24 8) (MInt2Float (extract v_6470 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6467 192 224) 24 8) (MInt2Float (extract v_6470 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_6467 224 256) 24 8) (MInt2Float (extract v_6470 224 256) 24 8)) 32))))))));
      pure ()
    pat_end;
    pattern fun (v_3452 : Mem) (v_3455 : reg (bv 128)) (v_3456 : reg (bv 128)) => do
      v_10436 <- getRegister v_3455;
      v_10439 <- evaluateAddress v_3452;
      v_10440 <- load v_10439 16;
      setRegister (lhs.of_reg v_3456) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10436 0 32) 24 8) (MInt2Float (extract v_10440 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10436 32 64) 24 8) (MInt2Float (extract v_10440 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10436 64 96) 24 8) (MInt2Float (extract v_10440 64 96) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10436 96 128) 24 8) (MInt2Float (extract v_10440 96 128) 24 8)) 32))));
      pure ()
    pat_end;
    pattern fun (v_3463 : Mem) (v_3464 : reg (bv 256)) (v_3465 : reg (bv 256)) => do
      v_10467 <- getRegister v_3464;
      v_10470 <- evaluateAddress v_3463;
      v_10471 <- load v_10470 32;
      setRegister (lhs.of_reg v_3465) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10467 0 32) 24 8) (MInt2Float (extract v_10471 0 32) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10467 32 64) 24 8) (MInt2Float (extract v_10471 32 64) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10467 64 96) 24 8) (MInt2Float (extract v_10471 64 96) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10467 96 128) 24 8) (MInt2Float (extract v_10471 96 128) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10467 128 160) 24 8) (MInt2Float (extract v_10471 128 160) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10467 160 192) 24 8) (MInt2Float (extract v_10471 160 192) 24 8)) 32) (concat (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10467 192 224) 24 8) (MInt2Float (extract v_10471 192 224) 24 8)) 32) (Float2MInt (_/Float__FLOAT (MInt2Float (extract v_10467 224 256) 24 8) (MInt2Float (extract v_10471 224 256) 24 8)) 32))))))));
      pure ()
    pat_end
