def vpackusdw1 : instruction :=
  definst "vpackusdw" $ do
    pattern fun (v_3366 : reg (bv 128)) (v_3367 : reg (bv 128)) (v_3368 : reg (bv 128)) => do
      v_6469 <- getRegister v_3366;
      v_6470 <- eval (extract v_6469 0 32);
      v_6476 <- eval (extract v_6469 32 64);
      v_6482 <- eval (extract v_6469 64 96);
      v_6488 <- eval (extract v_6469 96 128);
      v_6494 <- getRegister v_3367;
      v_6495 <- eval (extract v_6494 0 32);
      v_6501 <- eval (extract v_6494 32 64);
      v_6507 <- eval (extract v_6494 64 96);
      v_6513 <- eval (extract v_6494 96 128);
      setRegister (lhs.of_reg v_3368) (concat (mux (sgt v_6470 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6470 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6469 16 32))) (concat (mux (sgt v_6476 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6476 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6469 48 64))) (concat (mux (sgt v_6482 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6482 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6469 80 96))) (concat (mux (sgt v_6488 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6488 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6469 112 128))) (concat (mux (sgt v_6495 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6495 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6494 16 32))) (concat (mux (sgt v_6501 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6501 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6494 48 64))) (concat (mux (sgt v_6507 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6507 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6494 80 96))) (mux (sgt v_6513 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6513 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6494 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3377 : reg (bv 256)) (v_3378 : reg (bv 256)) (v_3379 : reg (bv 256)) => do
      v_6532 <- getRegister v_3377;
      v_6533 <- eval (extract v_6532 0 32);
      v_6539 <- eval (extract v_6532 32 64);
      v_6545 <- eval (extract v_6532 64 96);
      v_6551 <- eval (extract v_6532 96 128);
      v_6557 <- getRegister v_3378;
      v_6558 <- eval (extract v_6557 0 32);
      v_6564 <- eval (extract v_6557 32 64);
      v_6570 <- eval (extract v_6557 64 96);
      v_6576 <- eval (extract v_6557 96 128);
      v_6582 <- eval (extract v_6532 128 160);
      v_6588 <- eval (extract v_6532 160 192);
      v_6594 <- eval (extract v_6532 192 224);
      v_6600 <- eval (extract v_6532 224 256);
      v_6606 <- eval (extract v_6557 128 160);
      v_6612 <- eval (extract v_6557 160 192);
      v_6618 <- eval (extract v_6557 192 224);
      v_6624 <- eval (extract v_6557 224 256);
      setRegister (lhs.of_reg v_3379) (concat (mux (sgt v_6533 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6533 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6532 16 32))) (concat (mux (sgt v_6539 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6539 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6532 48 64))) (concat (mux (sgt v_6545 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6545 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6532 80 96))) (concat (mux (sgt v_6551 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6551 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6532 112 128))) (concat (mux (sgt v_6558 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6558 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6557 16 32))) (concat (mux (sgt v_6564 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6564 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6557 48 64))) (concat (mux (sgt v_6570 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6570 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6557 80 96))) (concat (mux (sgt v_6576 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6576 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6557 112 128))) (concat (mux (sgt v_6582 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6582 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6532 144 160))) (concat (mux (sgt v_6588 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6588 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6532 176 192))) (concat (mux (sgt v_6594 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6594 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6532 208 224))) (concat (mux (sgt v_6600 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6600 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6532 240 256))) (concat (mux (sgt v_6606 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6606 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6557 144 160))) (concat (mux (sgt v_6612 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6612 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6557 176 192))) (concat (mux (sgt v_6618 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6618 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6557 208 224))) (mux (sgt v_6624 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_6624 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_6557 240 256))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3361 : Mem) (v_3362 : reg (bv 128)) (v_3363 : reg (bv 128)) => do
      v_11525 <- evaluateAddress v_3361;
      v_11526 <- load v_11525 16;
      v_11527 <- eval (extract v_11526 0 32);
      v_11533 <- eval (extract v_11526 32 64);
      v_11539 <- eval (extract v_11526 64 96);
      v_11545 <- eval (extract v_11526 96 128);
      v_11551 <- getRegister v_3362;
      v_11552 <- eval (extract v_11551 0 32);
      v_11558 <- eval (extract v_11551 32 64);
      v_11564 <- eval (extract v_11551 64 96);
      v_11570 <- eval (extract v_11551 96 128);
      setRegister (lhs.of_reg v_3363) (concat (mux (sgt v_11527 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11527 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11526 16 32))) (concat (mux (sgt v_11533 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11533 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11526 48 64))) (concat (mux (sgt v_11539 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11539 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11526 80 96))) (concat (mux (sgt v_11545 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11545 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11526 112 128))) (concat (mux (sgt v_11552 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11552 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11551 16 32))) (concat (mux (sgt v_11558 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11558 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11551 48 64))) (concat (mux (sgt v_11564 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11564 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11551 80 96))) (mux (sgt v_11570 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11570 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11551 112 128))))))))));
      pure ()
    pat_end;
    pattern fun (v_3372 : Mem) (v_3373 : reg (bv 256)) (v_3374 : reg (bv 256)) => do
      v_11584 <- evaluateAddress v_3372;
      v_11585 <- load v_11584 32;
      v_11586 <- eval (extract v_11585 0 32);
      v_11592 <- eval (extract v_11585 32 64);
      v_11598 <- eval (extract v_11585 64 96);
      v_11604 <- eval (extract v_11585 96 128);
      v_11610 <- getRegister v_3373;
      v_11611 <- eval (extract v_11610 0 32);
      v_11617 <- eval (extract v_11610 32 64);
      v_11623 <- eval (extract v_11610 64 96);
      v_11629 <- eval (extract v_11610 96 128);
      v_11635 <- eval (extract v_11585 128 160);
      v_11641 <- eval (extract v_11585 160 192);
      v_11647 <- eval (extract v_11585 192 224);
      v_11653 <- eval (extract v_11585 224 256);
      v_11659 <- eval (extract v_11610 128 160);
      v_11665 <- eval (extract v_11610 160 192);
      v_11671 <- eval (extract v_11610 192 224);
      v_11677 <- eval (extract v_11610 224 256);
      setRegister (lhs.of_reg v_3374) (concat (mux (sgt v_11586 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11586 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11585 16 32))) (concat (mux (sgt v_11592 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11592 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11585 48 64))) (concat (mux (sgt v_11598 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11598 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11585 80 96))) (concat (mux (sgt v_11604 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11604 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11585 112 128))) (concat (mux (sgt v_11611 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11611 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11610 16 32))) (concat (mux (sgt v_11617 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11617 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11610 48 64))) (concat (mux (sgt v_11623 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11623 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11610 80 96))) (concat (mux (sgt v_11629 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11629 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11610 112 128))) (concat (mux (sgt v_11635 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11635 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11585 144 160))) (concat (mux (sgt v_11641 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11641 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11585 176 192))) (concat (mux (sgt v_11647 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11647 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11585 208 224))) (concat (mux (sgt v_11653 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11653 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11585 240 256))) (concat (mux (sgt v_11659 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11659 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11610 144 160))) (concat (mux (sgt v_11665 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11665 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11610 176 192))) (concat (mux (sgt v_11671 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11671 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11610 208 224))) (mux (sgt v_11677 (expression.bv_nat 32 65535)) (expression.bv_nat 16 65535) (mux (slt v_11677 (expression.bv_nat 32 0)) (expression.bv_nat 16 0) (extract v_11610 240 256))))))))))))))))));
      pure ()
    pat_end
