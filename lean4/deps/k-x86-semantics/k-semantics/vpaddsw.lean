def vpaddsw1 : instruction :=
  definst "vpaddsw" $ do
    pattern fun (v_2472 : reg (bv 128)) (v_2473 : reg (bv 128)) (v_2474 : reg (bv 128)) => do
      v_4605 <- getRegister v_2473;
      v_4608 <- getRegister v_2472;
      v_4611 <- eval (add (sext (extract v_4605 0 16) 32) (sext (extract v_4608 0 16) 32));
      v_4621 <- eval (add (sext (extract v_4605 16 32) 32) (sext (extract v_4608 16 32) 32));
      v_4631 <- eval (add (sext (extract v_4605 32 48) 32) (sext (extract v_4608 32 48) 32));
      v_4641 <- eval (add (sext (extract v_4605 48 64) 32) (sext (extract v_4608 48 64) 32));
      v_4651 <- eval (add (sext (extract v_4605 64 80) 32) (sext (extract v_4608 64 80) 32));
      v_4661 <- eval (add (sext (extract v_4605 80 96) 32) (sext (extract v_4608 80 96) 32));
      v_4671 <- eval (add (sext (extract v_4605 96 112) 32) (sext (extract v_4608 96 112) 32));
      v_4681 <- eval (add (sext (extract v_4605 112 128) 32) (sext (extract v_4608 112 128) 32));
      setRegister (lhs.of_reg v_2474) (concat (mux (sgt v_4611 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4611 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4611 16 32))) (concat (mux (sgt v_4621 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4621 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4621 16 32))) (concat (mux (sgt v_4631 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4631 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4631 16 32))) (concat (mux (sgt v_4641 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4641 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4641 16 32))) (concat (mux (sgt v_4651 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4651 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4651 16 32))) (concat (mux (sgt v_4661 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4661 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4661 16 32))) (concat (mux (sgt v_4671 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4671 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4671 16 32))) (mux (sgt v_4681 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4681 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4681 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2482 : reg (bv 256)) (v_2483 : reg (bv 256)) (v_2484 : reg (bv 256)) => do
      v_4700 <- getRegister v_2483;
      v_4703 <- getRegister v_2482;
      v_4706 <- eval (add (sext (extract v_4700 0 16) 32) (sext (extract v_4703 0 16) 32));
      v_4716 <- eval (add (sext (extract v_4700 16 32) 32) (sext (extract v_4703 16 32) 32));
      v_4726 <- eval (add (sext (extract v_4700 32 48) 32) (sext (extract v_4703 32 48) 32));
      v_4736 <- eval (add (sext (extract v_4700 48 64) 32) (sext (extract v_4703 48 64) 32));
      v_4746 <- eval (add (sext (extract v_4700 64 80) 32) (sext (extract v_4703 64 80) 32));
      v_4756 <- eval (add (sext (extract v_4700 80 96) 32) (sext (extract v_4703 80 96) 32));
      v_4766 <- eval (add (sext (extract v_4700 96 112) 32) (sext (extract v_4703 96 112) 32));
      v_4776 <- eval (add (sext (extract v_4700 112 128) 32) (sext (extract v_4703 112 128) 32));
      v_4786 <- eval (add (sext (extract v_4700 128 144) 32) (sext (extract v_4703 128 144) 32));
      v_4796 <- eval (add (sext (extract v_4700 144 160) 32) (sext (extract v_4703 144 160) 32));
      v_4806 <- eval (add (sext (extract v_4700 160 176) 32) (sext (extract v_4703 160 176) 32));
      v_4816 <- eval (add (sext (extract v_4700 176 192) 32) (sext (extract v_4703 176 192) 32));
      v_4826 <- eval (add (sext (extract v_4700 192 208) 32) (sext (extract v_4703 192 208) 32));
      v_4836 <- eval (add (sext (extract v_4700 208 224) 32) (sext (extract v_4703 208 224) 32));
      v_4846 <- eval (add (sext (extract v_4700 224 240) 32) (sext (extract v_4703 224 240) 32));
      v_4856 <- eval (add (sext (extract v_4700 240 256) 32) (sext (extract v_4703 240 256) 32));
      setRegister (lhs.of_reg v_2484) (concat (mux (sgt v_4706 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4706 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4706 16 32))) (concat (mux (sgt v_4716 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4716 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4716 16 32))) (concat (mux (sgt v_4726 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4726 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4726 16 32))) (concat (mux (sgt v_4736 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4736 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4736 16 32))) (concat (mux (sgt v_4746 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4746 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4746 16 32))) (concat (mux (sgt v_4756 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4756 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4756 16 32))) (concat (mux (sgt v_4766 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4766 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4766 16 32))) (concat (mux (sgt v_4776 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4776 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4776 16 32))) (concat (mux (sgt v_4786 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4786 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4786 16 32))) (concat (mux (sgt v_4796 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4796 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4796 16 32))) (concat (mux (sgt v_4806 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4806 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4806 16 32))) (concat (mux (sgt v_4816 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4816 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4816 16 32))) (concat (mux (sgt v_4826 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4826 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4826 16 32))) (concat (mux (sgt v_4836 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4836 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4836 16 32))) (concat (mux (sgt v_4846 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4846 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4846 16 32))) (mux (sgt v_4856 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_4856 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_4856 16 32))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2466 : Mem) (v_2467 : reg (bv 128)) (v_2468 : reg (bv 128)) => do
      v_13357 <- getRegister v_2467;
      v_13360 <- evaluateAddress v_2466;
      v_13361 <- load v_13360 16;
      v_13364 <- eval (add (sext (extract v_13357 0 16) 32) (sext (extract v_13361 0 16) 32));
      v_13374 <- eval (add (sext (extract v_13357 16 32) 32) (sext (extract v_13361 16 32) 32));
      v_13384 <- eval (add (sext (extract v_13357 32 48) 32) (sext (extract v_13361 32 48) 32));
      v_13394 <- eval (add (sext (extract v_13357 48 64) 32) (sext (extract v_13361 48 64) 32));
      v_13404 <- eval (add (sext (extract v_13357 64 80) 32) (sext (extract v_13361 64 80) 32));
      v_13414 <- eval (add (sext (extract v_13357 80 96) 32) (sext (extract v_13361 80 96) 32));
      v_13424 <- eval (add (sext (extract v_13357 96 112) 32) (sext (extract v_13361 96 112) 32));
      v_13434 <- eval (add (sext (extract v_13357 112 128) 32) (sext (extract v_13361 112 128) 32));
      setRegister (lhs.of_reg v_2468) (concat (mux (sgt v_13364 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13364 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13364 16 32))) (concat (mux (sgt v_13374 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13374 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13374 16 32))) (concat (mux (sgt v_13384 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13384 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13384 16 32))) (concat (mux (sgt v_13394 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13394 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13394 16 32))) (concat (mux (sgt v_13404 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13404 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13404 16 32))) (concat (mux (sgt v_13414 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13414 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13414 16 32))) (concat (mux (sgt v_13424 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13424 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13424 16 32))) (mux (sgt v_13434 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13434 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13434 16 32))))))))));
      pure ()
    pat_end;
    pattern fun (v_2477 : Mem) (v_2478 : reg (bv 256)) (v_2479 : reg (bv 256)) => do
      v_13448 <- getRegister v_2478;
      v_13451 <- evaluateAddress v_2477;
      v_13452 <- load v_13451 32;
      v_13455 <- eval (add (sext (extract v_13448 0 16) 32) (sext (extract v_13452 0 16) 32));
      v_13465 <- eval (add (sext (extract v_13448 16 32) 32) (sext (extract v_13452 16 32) 32));
      v_13475 <- eval (add (sext (extract v_13448 32 48) 32) (sext (extract v_13452 32 48) 32));
      v_13485 <- eval (add (sext (extract v_13448 48 64) 32) (sext (extract v_13452 48 64) 32));
      v_13495 <- eval (add (sext (extract v_13448 64 80) 32) (sext (extract v_13452 64 80) 32));
      v_13505 <- eval (add (sext (extract v_13448 80 96) 32) (sext (extract v_13452 80 96) 32));
      v_13515 <- eval (add (sext (extract v_13448 96 112) 32) (sext (extract v_13452 96 112) 32));
      v_13525 <- eval (add (sext (extract v_13448 112 128) 32) (sext (extract v_13452 112 128) 32));
      v_13535 <- eval (add (sext (extract v_13448 128 144) 32) (sext (extract v_13452 128 144) 32));
      v_13545 <- eval (add (sext (extract v_13448 144 160) 32) (sext (extract v_13452 144 160) 32));
      v_13555 <- eval (add (sext (extract v_13448 160 176) 32) (sext (extract v_13452 160 176) 32));
      v_13565 <- eval (add (sext (extract v_13448 176 192) 32) (sext (extract v_13452 176 192) 32));
      v_13575 <- eval (add (sext (extract v_13448 192 208) 32) (sext (extract v_13452 192 208) 32));
      v_13585 <- eval (add (sext (extract v_13448 208 224) 32) (sext (extract v_13452 208 224) 32));
      v_13595 <- eval (add (sext (extract v_13448 224 240) 32) (sext (extract v_13452 224 240) 32));
      v_13605 <- eval (add (sext (extract v_13448 240 256) 32) (sext (extract v_13452 240 256) 32));
      setRegister (lhs.of_reg v_2479) (concat (mux (sgt v_13455 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13455 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13455 16 32))) (concat (mux (sgt v_13465 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13465 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13465 16 32))) (concat (mux (sgt v_13475 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13475 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13475 16 32))) (concat (mux (sgt v_13485 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13485 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13485 16 32))) (concat (mux (sgt v_13495 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13495 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13495 16 32))) (concat (mux (sgt v_13505 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13505 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13505 16 32))) (concat (mux (sgt v_13515 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13515 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13515 16 32))) (concat (mux (sgt v_13525 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13525 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13525 16 32))) (concat (mux (sgt v_13535 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13535 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13535 16 32))) (concat (mux (sgt v_13545 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13545 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13545 16 32))) (concat (mux (sgt v_13555 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13555 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13555 16 32))) (concat (mux (sgt v_13565 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13565 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13565 16 32))) (concat (mux (sgt v_13575 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13575 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13575 16 32))) (concat (mux (sgt v_13585 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13585 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13585 16 32))) (concat (mux (sgt v_13595 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13595 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13595 16 32))) (mux (sgt v_13605 (expression.bv_nat 32 32767)) (expression.bv_nat 16 32767) (mux (slt v_13605 (expression.bv_nat 32 4294934528)) (expression.bv_nat 16 32768) (extract v_13605 16 32))))))))))))))))));
      pure ()
    pat_end
