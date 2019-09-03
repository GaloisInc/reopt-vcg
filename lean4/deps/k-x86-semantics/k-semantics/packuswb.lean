def packuswb1 : instruction :=
  definst "packuswb" $ do
    pattern fun (v_3102 : reg (bv 128)) (v_3103 : reg (bv 128)) => do
      v_5556 <- getRegister v_3102;
      v_5557 <- eval (extract v_5556 0 16);
      v_5563 <- eval (extract v_5556 16 32);
      v_5569 <- eval (extract v_5556 32 48);
      v_5575 <- eval (extract v_5556 48 64);
      v_5581 <- eval (extract v_5556 64 80);
      v_5587 <- eval (extract v_5556 80 96);
      v_5593 <- eval (extract v_5556 96 112);
      v_5599 <- eval (extract v_5556 112 128);
      v_5605 <- getRegister v_3103;
      v_5606 <- eval (extract v_5605 0 16);
      v_5612 <- eval (extract v_5605 16 32);
      v_5618 <- eval (extract v_5605 32 48);
      v_5624 <- eval (extract v_5605 48 64);
      v_5630 <- eval (extract v_5605 64 80);
      v_5636 <- eval (extract v_5605 80 96);
      v_5642 <- eval (extract v_5605 96 112);
      v_5648 <- eval (extract v_5605 112 128);
      setRegister (lhs.of_reg v_3103) (concat (mux (sgt v_5557 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5557 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5556 8 16))) (concat (mux (sgt v_5563 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5563 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5556 24 32))) (concat (mux (sgt v_5569 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5569 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5556 40 48))) (concat (mux (sgt v_5575 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5575 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5556 56 64))) (concat (mux (sgt v_5581 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5581 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5556 72 80))) (concat (mux (sgt v_5587 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5587 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5556 88 96))) (concat (mux (sgt v_5593 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5593 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5556 104 112))) (concat (mux (sgt v_5599 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5599 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5556 120 128))) (concat (mux (sgt v_5606 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5606 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5605 8 16))) (concat (mux (sgt v_5612 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5612 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5605 24 32))) (concat (mux (sgt v_5618 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5618 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5605 40 48))) (concat (mux (sgt v_5624 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5624 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5605 56 64))) (concat (mux (sgt v_5630 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5630 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5605 72 80))) (concat (mux (sgt v_5636 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5636 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5605 88 96))) (concat (mux (sgt v_5642 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5642 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5605 104 112))) (mux (sgt v_5648 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5648 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5605 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3097 : Mem) (v_3098 : reg (bv 128)) => do
      v_9655 <- evaluateAddress v_3097;
      v_9656 <- load v_9655 16;
      v_9657 <- eval (extract v_9656 0 16);
      v_9663 <- eval (extract v_9656 16 32);
      v_9669 <- eval (extract v_9656 32 48);
      v_9675 <- eval (extract v_9656 48 64);
      v_9681 <- eval (extract v_9656 64 80);
      v_9687 <- eval (extract v_9656 80 96);
      v_9693 <- eval (extract v_9656 96 112);
      v_9699 <- eval (extract v_9656 112 128);
      v_9705 <- getRegister v_3098;
      v_9706 <- eval (extract v_9705 0 16);
      v_9712 <- eval (extract v_9705 16 32);
      v_9718 <- eval (extract v_9705 32 48);
      v_9724 <- eval (extract v_9705 48 64);
      v_9730 <- eval (extract v_9705 64 80);
      v_9736 <- eval (extract v_9705 80 96);
      v_9742 <- eval (extract v_9705 96 112);
      v_9748 <- eval (extract v_9705 112 128);
      setRegister (lhs.of_reg v_3098) (concat (mux (sgt v_9657 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9657 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9656 8 16))) (concat (mux (sgt v_9663 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9663 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9656 24 32))) (concat (mux (sgt v_9669 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9669 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9656 40 48))) (concat (mux (sgt v_9675 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9675 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9656 56 64))) (concat (mux (sgt v_9681 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9681 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9656 72 80))) (concat (mux (sgt v_9687 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9687 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9656 88 96))) (concat (mux (sgt v_9693 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9693 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9656 104 112))) (concat (mux (sgt v_9699 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9699 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9656 120 128))) (concat (mux (sgt v_9706 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9706 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9705 8 16))) (concat (mux (sgt v_9712 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9712 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9705 24 32))) (concat (mux (sgt v_9718 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9718 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9705 40 48))) (concat (mux (sgt v_9724 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9724 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9705 56 64))) (concat (mux (sgt v_9730 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9730 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9705 72 80))) (concat (mux (sgt v_9736 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9736 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9705 88 96))) (concat (mux (sgt v_9742 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9742 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9705 104 112))) (mux (sgt v_9748 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9748 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9705 120 128))))))))))))))))));
      pure ()
    pat_end
