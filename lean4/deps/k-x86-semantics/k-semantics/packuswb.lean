def packuswb1 : instruction :=
  definst "packuswb" $ do
    pattern fun (v_3114 : reg (bv 128)) (v_3115 : reg (bv 128)) => do
      v_5587 <- getRegister v_3114;
      v_5588 <- eval (extract v_5587 0 16);
      v_5594 <- eval (extract v_5587 16 32);
      v_5600 <- eval (extract v_5587 32 48);
      v_5606 <- eval (extract v_5587 48 64);
      v_5612 <- eval (extract v_5587 64 80);
      v_5618 <- eval (extract v_5587 80 96);
      v_5624 <- eval (extract v_5587 96 112);
      v_5630 <- eval (extract v_5587 112 128);
      v_5636 <- getRegister v_3115;
      v_5637 <- eval (extract v_5636 0 16);
      v_5643 <- eval (extract v_5636 16 32);
      v_5649 <- eval (extract v_5636 32 48);
      v_5655 <- eval (extract v_5636 48 64);
      v_5661 <- eval (extract v_5636 64 80);
      v_5667 <- eval (extract v_5636 80 96);
      v_5673 <- eval (extract v_5636 96 112);
      v_5679 <- eval (extract v_5636 112 128);
      setRegister (lhs.of_reg v_3115) (concat (mux (sgt v_5588 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5588 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5587 8 16))) (concat (mux (sgt v_5594 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5594 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5587 24 32))) (concat (mux (sgt v_5600 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5600 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5587 40 48))) (concat (mux (sgt v_5606 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5606 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5587 56 64))) (concat (mux (sgt v_5612 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5612 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5587 72 80))) (concat (mux (sgt v_5618 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5618 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5587 88 96))) (concat (mux (sgt v_5624 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5624 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5587 104 112))) (concat (mux (sgt v_5630 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5630 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5587 120 128))) (concat (mux (sgt v_5637 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5637 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5636 8 16))) (concat (mux (sgt v_5643 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5643 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5636 24 32))) (concat (mux (sgt v_5649 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5649 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5636 40 48))) (concat (mux (sgt v_5655 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5655 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5636 56 64))) (concat (mux (sgt v_5661 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5661 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5636 72 80))) (concat (mux (sgt v_5667 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5667 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5636 88 96))) (concat (mux (sgt v_5673 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5673 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5636 104 112))) (mux (sgt v_5679 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_5679 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_5636 120 128))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3110 : Mem) (v_3111 : reg (bv 128)) => do
      v_9674 <- evaluateAddress v_3110;
      v_9675 <- load v_9674 16;
      v_9676 <- eval (extract v_9675 0 16);
      v_9682 <- eval (extract v_9675 16 32);
      v_9688 <- eval (extract v_9675 32 48);
      v_9694 <- eval (extract v_9675 48 64);
      v_9700 <- eval (extract v_9675 64 80);
      v_9706 <- eval (extract v_9675 80 96);
      v_9712 <- eval (extract v_9675 96 112);
      v_9718 <- eval (extract v_9675 112 128);
      v_9724 <- getRegister v_3111;
      v_9725 <- eval (extract v_9724 0 16);
      v_9731 <- eval (extract v_9724 16 32);
      v_9737 <- eval (extract v_9724 32 48);
      v_9743 <- eval (extract v_9724 48 64);
      v_9749 <- eval (extract v_9724 64 80);
      v_9755 <- eval (extract v_9724 80 96);
      v_9761 <- eval (extract v_9724 96 112);
      v_9767 <- eval (extract v_9724 112 128);
      setRegister (lhs.of_reg v_3111) (concat (mux (sgt v_9676 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9676 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9675 8 16))) (concat (mux (sgt v_9682 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9682 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9675 24 32))) (concat (mux (sgt v_9688 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9688 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9675 40 48))) (concat (mux (sgt v_9694 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9694 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9675 56 64))) (concat (mux (sgt v_9700 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9700 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9675 72 80))) (concat (mux (sgt v_9706 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9706 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9675 88 96))) (concat (mux (sgt v_9712 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9712 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9675 104 112))) (concat (mux (sgt v_9718 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9718 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9675 120 128))) (concat (mux (sgt v_9725 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9725 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9724 8 16))) (concat (mux (sgt v_9731 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9731 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9724 24 32))) (concat (mux (sgt v_9737 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9737 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9724 40 48))) (concat (mux (sgt v_9743 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9743 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9724 56 64))) (concat (mux (sgt v_9749 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9749 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9724 72 80))) (concat (mux (sgt v_9755 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9755 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9724 88 96))) (concat (mux (sgt v_9761 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9761 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9724 104 112))) (mux (sgt v_9767 (expression.bv_nat 16 255)) (expression.bv_nat 8 255) (mux (slt v_9767 (expression.bv_nat 16 0)) (expression.bv_nat 8 0) (extract v_9724 120 128))))))))))))))))));
      pure ()
    pat_end
