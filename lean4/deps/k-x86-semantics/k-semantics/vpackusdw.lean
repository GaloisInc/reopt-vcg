def vpackusdw1 : instruction :=
  definst "vpackusdw" $ do
    pattern fun (v_3341 : reg (bv 128)) (v_3342 : reg (bv 128)) (v_3343 : reg (bv 128)) => do
      v_6442 <- getRegister v_3341;
      v_6443 <- eval (extract v_6442 0 32);
      v_6449 <- eval (extract v_6442 32 64);
      v_6455 <- eval (extract v_6442 64 96);
      v_6461 <- eval (extract v_6442 96 128);
      v_6467 <- getRegister v_3342;
      v_6468 <- eval (extract v_6467 0 32);
      v_6474 <- eval (extract v_6467 32 64);
      v_6480 <- eval (extract v_6467 64 96);
      v_6486 <- eval (extract v_6467 96 128);
      setRegister (lhs.of_reg v_3343) (concat (mux (sgt v_6443 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6443 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6442 16 32))) (concat (mux (sgt v_6449 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6449 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6442 48 64))) (concat (mux (sgt v_6455 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6455 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6442 80 96))) (concat (mux (sgt v_6461 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6461 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6442 112 128))) (concat (mux (sgt v_6468 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6468 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6467 16 32))) (concat (mux (sgt v_6474 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6474 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6467 48 64))) (concat (mux (sgt v_6480 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6480 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6467 80 96))) (mux (sgt v_6486 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6486 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6467 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3353 : reg (bv 256)) (v_3354 : reg (bv 256)) (v_3355 : reg (bv 256)) => do
      v_6505 <- getRegister v_3353;
      v_6506 <- eval (extract v_6505 0 32);
      v_6512 <- eval (extract v_6505 32 64);
      v_6518 <- eval (extract v_6505 64 96);
      v_6524 <- eval (extract v_6505 96 128);
      v_6530 <- getRegister v_3354;
      v_6531 <- eval (extract v_6530 0 32);
      v_6537 <- eval (extract v_6530 32 64);
      v_6543 <- eval (extract v_6530 64 96);
      v_6549 <- eval (extract v_6530 96 128);
      v_6555 <- eval (extract v_6505 128 160);
      v_6561 <- eval (extract v_6505 160 192);
      v_6567 <- eval (extract v_6505 192 224);
      v_6573 <- eval (extract v_6505 224 256);
      v_6579 <- eval (extract v_6530 128 160);
      v_6585 <- eval (extract v_6530 160 192);
      v_6591 <- eval (extract v_6530 192 224);
      v_6597 <- eval (extract v_6530 224 256);
      setRegister (lhs.of_reg v_3355) (concat (mux (sgt v_6506 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6506 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6505 16 32))) (concat (mux (sgt v_6512 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6512 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6505 48 64))) (concat (mux (sgt v_6518 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6518 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6505 80 96))) (concat (mux (sgt v_6524 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6524 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6505 112 128))) (concat (mux (sgt v_6531 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6531 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6530 16 32))) (concat (mux (sgt v_6537 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6537 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6530 48 64))) (concat (mux (sgt v_6543 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6543 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6530 80 96))) (concat (mux (sgt v_6549 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6549 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6530 112 128))) (concat (mux (sgt v_6555 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6555 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6505 144 160))) (concat (mux (sgt v_6561 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6561 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6505 176 192))) (concat (mux (sgt v_6567 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6567 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6505 208 224))) (concat (mux (sgt v_6573 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6573 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6505 240 256))) (concat (mux (sgt v_6579 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6579 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6530 144 160))) (concat (mux (sgt v_6585 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6585 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6530 176 192))) (concat (mux (sgt v_6591 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6591 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6530 208 224))) (mux (sgt v_6597 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6597 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6530 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3336 : Mem) (v_3337 : reg (bv 128)) (v_3338 : reg (bv 128)) => do
      v_11498 <- evaluateAddress v_3336;
      v_11499 <- load v_11498 16;
      v_11500 <- eval (extract v_11499 0 32);
      v_11506 <- eval (extract v_11499 32 64);
      v_11512 <- eval (extract v_11499 64 96);
      v_11518 <- eval (extract v_11499 96 128);
      v_11524 <- getRegister v_3337;
      v_11525 <- eval (extract v_11524 0 32);
      v_11531 <- eval (extract v_11524 32 64);
      v_11537 <- eval (extract v_11524 64 96);
      v_11543 <- eval (extract v_11524 96 128);
      setRegister (lhs.of_reg v_3338) (concat (mux (sgt v_11500 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11500 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11499 16 32))) (concat (mux (sgt v_11506 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11506 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11499 48 64))) (concat (mux (sgt v_11512 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11512 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11499 80 96))) (concat (mux (sgt v_11518 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11518 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11499 112 128))) (concat (mux (sgt v_11525 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11525 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11524 16 32))) (concat (mux (sgt v_11531 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11531 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11524 48 64))) (concat (mux (sgt v_11537 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11537 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11524 80 96))) (mux (sgt v_11543 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11543 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11524 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3347 : Mem) (v_3348 : reg (bv 256)) (v_3349 : reg (bv 256)) => do
      v_11557 <- evaluateAddress v_3347;
      v_11558 <- load v_11557 32;
      v_11559 <- eval (extract v_11558 0 32);
      v_11565 <- eval (extract v_11558 32 64);
      v_11571 <- eval (extract v_11558 64 96);
      v_11577 <- eval (extract v_11558 96 128);
      v_11583 <- getRegister v_3348;
      v_11584 <- eval (extract v_11583 0 32);
      v_11590 <- eval (extract v_11583 32 64);
      v_11596 <- eval (extract v_11583 64 96);
      v_11602 <- eval (extract v_11583 96 128);
      v_11608 <- eval (extract v_11558 128 160);
      v_11614 <- eval (extract v_11558 160 192);
      v_11620 <- eval (extract v_11558 192 224);
      v_11626 <- eval (extract v_11558 224 256);
      v_11632 <- eval (extract v_11583 128 160);
      v_11638 <- eval (extract v_11583 160 192);
      v_11644 <- eval (extract v_11583 192 224);
      v_11650 <- eval (extract v_11583 224 256);
      setRegister (lhs.of_reg v_3349) (concat (mux (sgt v_11559 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11559 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11558 16 32))) (concat (mux (sgt v_11565 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11565 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11558 48 64))) (concat (mux (sgt v_11571 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11571 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11558 80 96))) (concat (mux (sgt v_11577 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11577 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11558 112 128))) (concat (mux (sgt v_11584 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11584 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11583 16 32))) (concat (mux (sgt v_11590 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11590 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11583 48 64))) (concat (mux (sgt v_11596 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11596 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11583 80 96))) (concat (mux (sgt v_11602 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11602 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11583 112 128))) (concat (mux (sgt v_11608 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11608 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11558 144 160))) (concat (mux (sgt v_11614 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11614 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11558 176 192))) (concat (mux (sgt v_11620 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11620 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11558 208 224))) (concat (mux (sgt v_11626 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11626 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11558 240 256))) (concat (mux (sgt v_11632 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11632 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11583 144 160))) (concat (mux (sgt v_11638 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11638 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11583 176 192))) (concat (mux (sgt v_11644 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11644 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11583 208 224))) (mux (sgt v_11650 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11650 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11583 240 256))))))))))))))))));
      pure ()
    pat_end
