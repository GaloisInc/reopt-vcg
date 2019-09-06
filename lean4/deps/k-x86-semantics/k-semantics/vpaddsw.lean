def vpaddsw1 : instruction :=
  definst "vpaddsw" $ do
    pattern fun (v_2498 : reg (bv 128)) (v_2499 : reg (bv 128)) (v_2500 : reg (bv 128)) => do
      v_4632 <- getRegister v_2499;
      v_4635 <- getRegister v_2498;
      v_4638 <- eval (add (sext (extract v_4632 0 16) 32) (sext (extract v_4635 0 16) 32));
      v_4648 <- eval (add (sext (extract v_4632 16 32) 32) (sext (extract v_4635 16 32) 32));
      v_4658 <- eval (add (sext (extract v_4632 32 48) 32) (sext (extract v_4635 32 48) 32));
      v_4668 <- eval (add (sext (extract v_4632 48 64) 32) (sext (extract v_4635 48 64) 32));
      v_4678 <- eval (add (sext (extract v_4632 64 80) 32) (sext (extract v_4635 64 80) 32));
      v_4688 <- eval (add (sext (extract v_4632 80 96) 32) (sext (extract v_4635 80 96) 32));
      v_4698 <- eval (add (sext (extract v_4632 96 112) 32) (sext (extract v_4635 96 112) 32));
      v_4708 <- eval (add (sext (extract v_4632 112 128) 32) (sext (extract v_4635 112 128) 32));
      setRegister (lhs.of_reg v_2500) (concat (mux (sgt v_4638 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4638 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4638 16 32))) (concat (mux (sgt v_4648 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4648 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4648 16 32))) (concat (mux (sgt v_4658 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4658 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4658 16 32))) (concat (mux (sgt v_4668 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4668 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4668 16 32))) (concat (mux (sgt v_4678 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4678 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4678 16 32))) (concat (mux (sgt v_4688 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4688 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4688 16 32))) (concat (mux (sgt v_4698 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4698 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4698 16 32))) (mux (sgt v_4708 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4708 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4708 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2509 : reg (bv 256)) (v_2510 : reg (bv 256)) (v_2511 : reg (bv 256)) => do
      v_4727 <- getRegister v_2510;
      v_4730 <- getRegister v_2509;
      v_4733 <- eval (add (sext (extract v_4727 0 16) 32) (sext (extract v_4730 0 16) 32));
      v_4743 <- eval (add (sext (extract v_4727 16 32) 32) (sext (extract v_4730 16 32) 32));
      v_4753 <- eval (add (sext (extract v_4727 32 48) 32) (sext (extract v_4730 32 48) 32));
      v_4763 <- eval (add (sext (extract v_4727 48 64) 32) (sext (extract v_4730 48 64) 32));
      v_4773 <- eval (add (sext (extract v_4727 64 80) 32) (sext (extract v_4730 64 80) 32));
      v_4783 <- eval (add (sext (extract v_4727 80 96) 32) (sext (extract v_4730 80 96) 32));
      v_4793 <- eval (add (sext (extract v_4727 96 112) 32) (sext (extract v_4730 96 112) 32));
      v_4803 <- eval (add (sext (extract v_4727 112 128) 32) (sext (extract v_4730 112 128) 32));
      v_4813 <- eval (add (sext (extract v_4727 128 144) 32) (sext (extract v_4730 128 144) 32));
      v_4823 <- eval (add (sext (extract v_4727 144 160) 32) (sext (extract v_4730 144 160) 32));
      v_4833 <- eval (add (sext (extract v_4727 160 176) 32) (sext (extract v_4730 160 176) 32));
      v_4843 <- eval (add (sext (extract v_4727 176 192) 32) (sext (extract v_4730 176 192) 32));
      v_4853 <- eval (add (sext (extract v_4727 192 208) 32) (sext (extract v_4730 192 208) 32));
      v_4863 <- eval (add (sext (extract v_4727 208 224) 32) (sext (extract v_4730 208 224) 32));
      v_4873 <- eval (add (sext (extract v_4727 224 240) 32) (sext (extract v_4730 224 240) 32));
      v_4883 <- eval (add (sext (extract v_4727 240 256) 32) (sext (extract v_4730 240 256) 32));
      setRegister (lhs.of_reg v_2511) (concat (mux (sgt v_4733 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4733 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4733 16 32))) (concat (mux (sgt v_4743 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4743 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4743 16 32))) (concat (mux (sgt v_4753 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4753 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4753 16 32))) (concat (mux (sgt v_4763 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4763 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4763 16 32))) (concat (mux (sgt v_4773 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4773 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4773 16 32))) (concat (mux (sgt v_4783 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4783 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4783 16 32))) (concat (mux (sgt v_4793 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4793 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4793 16 32))) (concat (mux (sgt v_4803 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4803 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4803 16 32))) (concat (mux (sgt v_4813 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4813 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4813 16 32))) (concat (mux (sgt v_4823 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4823 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4823 16 32))) (concat (mux (sgt v_4833 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4833 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4833 16 32))) (concat (mux (sgt v_4843 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4843 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4843 16 32))) (concat (mux (sgt v_4853 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4853 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4853 16 32))) (concat (mux (sgt v_4863 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4863 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4863 16 32))) (concat (mux (sgt v_4873 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4873 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4873 16 32))) (mux (sgt v_4883 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4883 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4883 16 32))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2493 : Mem) (v_2494 : reg (bv 128)) (v_2495 : reg (bv 128)) => do
      v_13384 <- getRegister v_2494;
      v_13387 <- evaluateAddress v_2493;
      v_13388 <- load v_13387 16;
      v_13391 <- eval (add (sext (extract v_13384 0 16) 32) (sext (extract v_13388 0 16) 32));
      v_13401 <- eval (add (sext (extract v_13384 16 32) 32) (sext (extract v_13388 16 32) 32));
      v_13411 <- eval (add (sext (extract v_13384 32 48) 32) (sext (extract v_13388 32 48) 32));
      v_13421 <- eval (add (sext (extract v_13384 48 64) 32) (sext (extract v_13388 48 64) 32));
      v_13431 <- eval (add (sext (extract v_13384 64 80) 32) (sext (extract v_13388 64 80) 32));
      v_13441 <- eval (add (sext (extract v_13384 80 96) 32) (sext (extract v_13388 80 96) 32));
      v_13451 <- eval (add (sext (extract v_13384 96 112) 32) (sext (extract v_13388 96 112) 32));
      v_13461 <- eval (add (sext (extract v_13384 112 128) 32) (sext (extract v_13388 112 128) 32));
      setRegister (lhs.of_reg v_2495) (concat (mux (sgt v_13391 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13391 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13391 16 32))) (concat (mux (sgt v_13401 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13401 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13401 16 32))) (concat (mux (sgt v_13411 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13411 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13411 16 32))) (concat (mux (sgt v_13421 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13421 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13421 16 32))) (concat (mux (sgt v_13431 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13431 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13431 16 32))) (concat (mux (sgt v_13441 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13441 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13441 16 32))) (concat (mux (sgt v_13451 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13451 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13451 16 32))) (mux (sgt v_13461 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13461 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13461 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2504 : Mem) (v_2505 : reg (bv 256)) (v_2506 : reg (bv 256)) => do
      v_13475 <- getRegister v_2505;
      v_13478 <- evaluateAddress v_2504;
      v_13479 <- load v_13478 32;
      v_13482 <- eval (add (sext (extract v_13475 0 16) 32) (sext (extract v_13479 0 16) 32));
      v_13492 <- eval (add (sext (extract v_13475 16 32) 32) (sext (extract v_13479 16 32) 32));
      v_13502 <- eval (add (sext (extract v_13475 32 48) 32) (sext (extract v_13479 32 48) 32));
      v_13512 <- eval (add (sext (extract v_13475 48 64) 32) (sext (extract v_13479 48 64) 32));
      v_13522 <- eval (add (sext (extract v_13475 64 80) 32) (sext (extract v_13479 64 80) 32));
      v_13532 <- eval (add (sext (extract v_13475 80 96) 32) (sext (extract v_13479 80 96) 32));
      v_13542 <- eval (add (sext (extract v_13475 96 112) 32) (sext (extract v_13479 96 112) 32));
      v_13552 <- eval (add (sext (extract v_13475 112 128) 32) (sext (extract v_13479 112 128) 32));
      v_13562 <- eval (add (sext (extract v_13475 128 144) 32) (sext (extract v_13479 128 144) 32));
      v_13572 <- eval (add (sext (extract v_13475 144 160) 32) (sext (extract v_13479 144 160) 32));
      v_13582 <- eval (add (sext (extract v_13475 160 176) 32) (sext (extract v_13479 160 176) 32));
      v_13592 <- eval (add (sext (extract v_13475 176 192) 32) (sext (extract v_13479 176 192) 32));
      v_13602 <- eval (add (sext (extract v_13475 192 208) 32) (sext (extract v_13479 192 208) 32));
      v_13612 <- eval (add (sext (extract v_13475 208 224) 32) (sext (extract v_13479 208 224) 32));
      v_13622 <- eval (add (sext (extract v_13475 224 240) 32) (sext (extract v_13479 224 240) 32));
      v_13632 <- eval (add (sext (extract v_13475 240 256) 32) (sext (extract v_13479 240 256) 32));
      setRegister (lhs.of_reg v_2506) (concat (mux (sgt v_13482 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13482 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13482 16 32))) (concat (mux (sgt v_13492 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13492 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13492 16 32))) (concat (mux (sgt v_13502 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13502 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13502 16 32))) (concat (mux (sgt v_13512 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13512 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13512 16 32))) (concat (mux (sgt v_13522 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13522 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13522 16 32))) (concat (mux (sgt v_13532 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13532 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13532 16 32))) (concat (mux (sgt v_13542 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13542 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13542 16 32))) (concat (mux (sgt v_13552 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13552 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13552 16 32))) (concat (mux (sgt v_13562 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13562 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13562 16 32))) (concat (mux (sgt v_13572 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13572 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13572 16 32))) (concat (mux (sgt v_13582 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13582 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13582 16 32))) (concat (mux (sgt v_13592 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13592 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13592 16 32))) (concat (mux (sgt v_13602 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13602 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13602 16 32))) (concat (mux (sgt v_13612 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13612 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13612 16 32))) (concat (mux (sgt v_13622 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13622 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13622 16 32))) (mux (sgt v_13632 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13632 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13632 16 32))))))))))))))))));
      pure ()
    pat_end
