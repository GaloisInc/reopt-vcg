def vpaddq1 : instruction :=
  definst "vpaddq" $ do
    pattern fun (v_3454 : reg (bv 128)) (v_3455 : reg (bv 128)) (v_3456 : reg (bv 128)) => do
      v_7269 <- getRegister v_3455;
      v_7271 <- getRegister v_3454;
      setRegister (lhs.of_reg v_3456) (concat (add (extract v_7269 0 64) (extract v_7271 0 64)) (add (extract v_7269 64 128) (extract v_7271 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3465 : reg (bv 256)) (v_3466 : reg (bv 256)) (v_3467 : reg (bv 256)) => do
      v_7284 <- getRegister v_3466;
      v_7286 <- getRegister v_3465;
      setRegister (lhs.of_reg v_3467) (concat (add (extract v_7284 0 64) (extract v_7286 0 64)) (concat (add (extract v_7284 64 128) (extract v_7286 64 128)) (concat (add (extract v_7284 128 192) (extract v_7286 128 192)) (add (extract v_7284 192 256) (extract v_7286 192 256)))));
      pure ()
    pat_end;
    pattern fun (v_3449 : Mem) (v_3450 : reg (bv 128)) (v_3451 : reg (bv 128)) => do
      v_12293 <- getRegister v_3450;
      v_12295 <- evaluateAddress v_3449;
      v_12296 <- load v_12295 16;
      setRegister (lhs.of_reg v_3451) (concat (add (extract v_12293 0 64) (extract v_12296 0 64)) (add (extract v_12293 64 128) (extract v_12296 64 128)));
      pure ()
    pat_end;
    pattern fun (v_3460 : Mem) (v_3461 : reg (bv 256)) (v_3462 : reg (bv 256)) => do
      v_12304 <- getRegister v_3461;
      v_12306 <- evaluateAddress v_3460;
      v_12307 <- load v_12306 32;
      setRegister (lhs.of_reg v_3462) (concat (add (extract v_12304 0 64) (extract v_12307 0 64)) (concat (add (extract v_12304 64 128) (extract v_12307 64 128)) (concat (add (extract v_12304 128 192) (extract v_12307 128 192)) (add (extract v_12304 192 256) (extract v_12307 192 256)))));
      pure ()
    pat_end
