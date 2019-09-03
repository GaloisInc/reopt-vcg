def vpermilps1 : instruction :=
  definst "vpermilps" $ do
    pattern fun (v_3014 : imm int) (v_3018 : reg (bv 128)) (v_3019 : reg (bv 128)) => do
      v_8492 <- eval (handleImmediateWithSignExtend v_3014 8 8);
      v_8493 <- eval (extract v_8492 0 2);
      v_8495 <- getRegister v_3018;
      v_8496 <- eval (extract v_8495 96 128);
      v_8498 <- eval (extract v_8495 64 96);
      v_8500 <- eval (extract v_8495 32 64);
      v_8501 <- eval (extract v_8495 0 32);
      v_8505 <- eval (extract v_8492 2 4);
      v_8512 <- eval (extract v_8492 4 6);
      v_8519 <- eval (extract v_8492 6 8);
      setRegister (lhs.of_reg v_3019) (concat (mux (eq v_8493 (expression.bv_nat 2 0)) v_8496 (mux (eq v_8493 (expression.bv_nat 2 1)) v_8498 (mux (eq v_8493 (expression.bv_nat 2 2)) v_8500 v_8501))) (concat (mux (eq v_8505 (expression.bv_nat 2 0)) v_8496 (mux (eq v_8505 (expression.bv_nat 2 1)) v_8498 (mux (eq v_8505 (expression.bv_nat 2 2)) v_8500 v_8501))) (concat (mux (eq v_8512 (expression.bv_nat 2 0)) v_8496 (mux (eq v_8512 (expression.bv_nat 2 1)) v_8498 (mux (eq v_8512 (expression.bv_nat 2 2)) v_8500 v_8501))) (mux (eq v_8519 (expression.bv_nat 2 0)) v_8496 (mux (eq v_8519 (expression.bv_nat 2 1)) v_8498 (mux (eq v_8519 (expression.bv_nat 2 2)) v_8500 v_8501))))));
      pure ()
    pat_end;
    pattern fun (v_3028 : reg (bv 128)) (v_3029 : reg (bv 128)) (v_3030 : reg (bv 128)) => do
      v_8535 <- getRegister v_3028;
      v_8536 <- eval (extract v_8535 30 32);
      v_8538 <- getRegister v_3029;
      v_8539 <- eval (extract v_8538 96 128);
      v_8541 <- eval (extract v_8538 64 96);
      v_8543 <- eval (extract v_8538 32 64);
      v_8544 <- eval (extract v_8538 0 32);
      v_8548 <- eval (extract v_8535 62 64);
      v_8555 <- eval (extract v_8535 94 96);
      v_8562 <- eval (extract v_8535 126 128);
      setRegister (lhs.of_reg v_3030) (concat (mux (eq v_8536 (expression.bv_nat 2 0)) v_8539 (mux (eq v_8536 (expression.bv_nat 2 1)) v_8541 (mux (eq v_8536 (expression.bv_nat 2 2)) v_8543 v_8544))) (concat (mux (eq v_8548 (expression.bv_nat 2 0)) v_8539 (mux (eq v_8548 (expression.bv_nat 2 1)) v_8541 (mux (eq v_8548 (expression.bv_nat 2 2)) v_8543 v_8544))) (concat (mux (eq v_8555 (expression.bv_nat 2 0)) v_8539 (mux (eq v_8555 (expression.bv_nat 2 1)) v_8541 (mux (eq v_8555 (expression.bv_nat 2 2)) v_8543 v_8544))) (mux (eq v_8562 (expression.bv_nat 2 0)) v_8539 (mux (eq v_8562 (expression.bv_nat 2 1)) v_8541 (mux (eq v_8562 (expression.bv_nat 2 2)) v_8543 v_8544))))));
      pure ()
    pat_end;
    pattern fun (v_3036 : imm int) (v_3040 : reg (bv 256)) (v_3041 : reg (bv 256)) => do
      v_8578 <- eval (handleImmediateWithSignExtend v_3036 8 8);
      v_8579 <- eval (extract v_8578 0 2);
      v_8580 <- eval (eq v_8579 (expression.bv_nat 2 0));
      v_8581 <- getRegister v_3040;
      v_8582 <- eval (extract v_8581 96 128);
      v_8583 <- eval (eq v_8579 (expression.bv_nat 2 1));
      v_8584 <- eval (extract v_8581 64 96);
      v_8585 <- eval (eq v_8579 (expression.bv_nat 2 2));
      v_8586 <- eval (extract v_8581 32 64);
      v_8587 <- eval (extract v_8581 0 32);
      v_8591 <- eval (extract v_8578 2 4);
      v_8592 <- eval (eq v_8591 (expression.bv_nat 2 0));
      v_8593 <- eval (eq v_8591 (expression.bv_nat 2 1));
      v_8594 <- eval (eq v_8591 (expression.bv_nat 2 2));
      v_8598 <- eval (extract v_8578 4 6);
      v_8599 <- eval (eq v_8598 (expression.bv_nat 2 0));
      v_8600 <- eval (eq v_8598 (expression.bv_nat 2 1));
      v_8601 <- eval (eq v_8598 (expression.bv_nat 2 2));
      v_8605 <- eval (extract v_8578 6 8);
      v_8606 <- eval (eq v_8605 (expression.bv_nat 2 0));
      v_8607 <- eval (eq v_8605 (expression.bv_nat 2 1));
      v_8608 <- eval (eq v_8605 (expression.bv_nat 2 2));
      v_8612 <- eval (extract v_8581 224 256);
      v_8613 <- eval (extract v_8581 192 224);
      v_8614 <- eval (extract v_8581 160 192);
      v_8615 <- eval (extract v_8581 128 160);
      setRegister (lhs.of_reg v_3041) (concat (mux v_8580 v_8582 (mux v_8583 v_8584 (mux v_8585 v_8586 v_8587))) (concat (mux v_8592 v_8582 (mux v_8593 v_8584 (mux v_8594 v_8586 v_8587))) (concat (mux v_8599 v_8582 (mux v_8600 v_8584 (mux v_8601 v_8586 v_8587))) (concat (mux v_8606 v_8582 (mux v_8607 v_8584 (mux v_8608 v_8586 v_8587))) (concat (mux v_8580 v_8612 (mux v_8583 v_8613 (mux v_8585 v_8614 v_8615))) (concat (mux v_8592 v_8612 (mux v_8593 v_8613 (mux v_8594 v_8614 v_8615))) (concat (mux v_8599 v_8612 (mux v_8600 v_8613 (mux v_8601 v_8614 v_8615))) (mux v_8606 v_8612 (mux v_8607 v_8613 (mux v_8608 v_8614 v_8615))))))))));
      pure ()
    pat_end;
    pattern fun (v_3050 : reg (bv 256)) (v_3051 : reg (bv 256)) (v_3052 : reg (bv 256)) => do
      v_8641 <- getRegister v_3050;
      v_8642 <- eval (extract v_8641 30 32);
      v_8644 <- getRegister v_3051;
      v_8645 <- eval (extract v_8644 96 128);
      v_8647 <- eval (extract v_8644 64 96);
      v_8649 <- eval (extract v_8644 32 64);
      v_8650 <- eval (extract v_8644 0 32);
      v_8654 <- eval (extract v_8641 62 64);
      v_8661 <- eval (extract v_8641 94 96);
      v_8668 <- eval (extract v_8641 126 128);
      v_8675 <- eval (extract v_8641 158 160);
      v_8677 <- eval (extract v_8644 224 256);
      v_8679 <- eval (extract v_8644 192 224);
      v_8681 <- eval (extract v_8644 160 192);
      v_8682 <- eval (extract v_8644 128 160);
      v_8686 <- eval (extract v_8641 190 192);
      v_8693 <- eval (extract v_8641 222 224);
      v_8700 <- eval (extract v_8641 254 256);
      setRegister (lhs.of_reg v_3052) (concat (mux (eq v_8642 (expression.bv_nat 2 0)) v_8645 (mux (eq v_8642 (expression.bv_nat 2 1)) v_8647 (mux (eq v_8642 (expression.bv_nat 2 2)) v_8649 v_8650))) (concat (mux (eq v_8654 (expression.bv_nat 2 0)) v_8645 (mux (eq v_8654 (expression.bv_nat 2 1)) v_8647 (mux (eq v_8654 (expression.bv_nat 2 2)) v_8649 v_8650))) (concat (mux (eq v_8661 (expression.bv_nat 2 0)) v_8645 (mux (eq v_8661 (expression.bv_nat 2 1)) v_8647 (mux (eq v_8661 (expression.bv_nat 2 2)) v_8649 v_8650))) (concat (mux (eq v_8668 (expression.bv_nat 2 0)) v_8645 (mux (eq v_8668 (expression.bv_nat 2 1)) v_8647 (mux (eq v_8668 (expression.bv_nat 2 2)) v_8649 v_8650))) (concat (mux (eq v_8675 (expression.bv_nat 2 0)) v_8677 (mux (eq v_8675 (expression.bv_nat 2 1)) v_8679 (mux (eq v_8675 (expression.bv_nat 2 2)) v_8681 v_8682))) (concat (mux (eq v_8686 (expression.bv_nat 2 0)) v_8677 (mux (eq v_8686 (expression.bv_nat 2 1)) v_8679 (mux (eq v_8686 (expression.bv_nat 2 2)) v_8681 v_8682))) (concat (mux (eq v_8693 (expression.bv_nat 2 0)) v_8677 (mux (eq v_8693 (expression.bv_nat 2 1)) v_8679 (mux (eq v_8693 (expression.bv_nat 2 2)) v_8681 v_8682))) (mux (eq v_8700 (expression.bv_nat 2 0)) v_8677 (mux (eq v_8700 (expression.bv_nat 2 1)) v_8679 (mux (eq v_8700 (expression.bv_nat 2 2)) v_8681 v_8682))))))))));
      pure ()
    pat_end;
    pattern fun (v_3009 : imm int) (v_3012 : Mem) (v_3013 : reg (bv 128)) => do
      v_17634 <- eval (handleImmediateWithSignExtend v_3009 8 8);
      v_17635 <- eval (extract v_17634 0 2);
      v_17637 <- evaluateAddress v_3012;
      v_17638 <- load v_17637 16;
      v_17639 <- eval (extract v_17638 96 128);
      v_17641 <- eval (extract v_17638 64 96);
      v_17643 <- eval (extract v_17638 32 64);
      v_17644 <- eval (extract v_17638 0 32);
      v_17648 <- eval (extract v_17634 2 4);
      v_17655 <- eval (extract v_17634 4 6);
      v_17662 <- eval (extract v_17634 6 8);
      setRegister (lhs.of_reg v_3013) (concat (mux (eq v_17635 (expression.bv_nat 2 0)) v_17639 (mux (eq v_17635 (expression.bv_nat 2 1)) v_17641 (mux (eq v_17635 (expression.bv_nat 2 2)) v_17643 v_17644))) (concat (mux (eq v_17648 (expression.bv_nat 2 0)) v_17639 (mux (eq v_17648 (expression.bv_nat 2 1)) v_17641 (mux (eq v_17648 (expression.bv_nat 2 2)) v_17643 v_17644))) (concat (mux (eq v_17655 (expression.bv_nat 2 0)) v_17639 (mux (eq v_17655 (expression.bv_nat 2 1)) v_17641 (mux (eq v_17655 (expression.bv_nat 2 2)) v_17643 v_17644))) (mux (eq v_17662 (expression.bv_nat 2 0)) v_17639 (mux (eq v_17662 (expression.bv_nat 2 1)) v_17641 (mux (eq v_17662 (expression.bv_nat 2 2)) v_17643 v_17644))))));
      pure ()
    pat_end;
    pattern fun (v_3022 : Mem) (v_3023 : reg (bv 128)) (v_3024 : reg (bv 128)) => do
      v_17673 <- evaluateAddress v_3022;
      v_17674 <- load v_17673 16;
      v_17675 <- eval (extract v_17674 30 32);
      v_17677 <- getRegister v_3023;
      v_17678 <- eval (extract v_17677 96 128);
      v_17680 <- eval (extract v_17677 64 96);
      v_17682 <- eval (extract v_17677 32 64);
      v_17683 <- eval (extract v_17677 0 32);
      v_17687 <- eval (extract v_17674 62 64);
      v_17694 <- eval (extract v_17674 94 96);
      v_17701 <- eval (extract v_17674 126 128);
      setRegister (lhs.of_reg v_3024) (concat (mux (eq v_17675 (expression.bv_nat 2 0)) v_17678 (mux (eq v_17675 (expression.bv_nat 2 1)) v_17680 (mux (eq v_17675 (expression.bv_nat 2 2)) v_17682 v_17683))) (concat (mux (eq v_17687 (expression.bv_nat 2 0)) v_17678 (mux (eq v_17687 (expression.bv_nat 2 1)) v_17680 (mux (eq v_17687 (expression.bv_nat 2 2)) v_17682 v_17683))) (concat (mux (eq v_17694 (expression.bv_nat 2 0)) v_17678 (mux (eq v_17694 (expression.bv_nat 2 1)) v_17680 (mux (eq v_17694 (expression.bv_nat 2 2)) v_17682 v_17683))) (mux (eq v_17701 (expression.bv_nat 2 0)) v_17678 (mux (eq v_17701 (expression.bv_nat 2 1)) v_17680 (mux (eq v_17701 (expression.bv_nat 2 2)) v_17682 v_17683))))));
      pure ()
    pat_end;
    pattern fun (v_3031 : imm int) (v_3034 : Mem) (v_3035 : reg (bv 256)) => do
      v_17712 <- eval (handleImmediateWithSignExtend v_3031 8 8);
      v_17713 <- eval (extract v_17712 0 2);
      v_17714 <- eval (eq v_17713 (expression.bv_nat 2 0));
      v_17715 <- evaluateAddress v_3034;
      v_17716 <- load v_17715 32;
      v_17717 <- eval (extract v_17716 96 128);
      v_17718 <- eval (eq v_17713 (expression.bv_nat 2 1));
      v_17719 <- eval (extract v_17716 64 96);
      v_17720 <- eval (eq v_17713 (expression.bv_nat 2 2));
      v_17721 <- eval (extract v_17716 32 64);
      v_17722 <- eval (extract v_17716 0 32);
      v_17726 <- eval (extract v_17712 2 4);
      v_17727 <- eval (eq v_17726 (expression.bv_nat 2 0));
      v_17728 <- eval (eq v_17726 (expression.bv_nat 2 1));
      v_17729 <- eval (eq v_17726 (expression.bv_nat 2 2));
      v_17733 <- eval (extract v_17712 4 6);
      v_17734 <- eval (eq v_17733 (expression.bv_nat 2 0));
      v_17735 <- eval (eq v_17733 (expression.bv_nat 2 1));
      v_17736 <- eval (eq v_17733 (expression.bv_nat 2 2));
      v_17740 <- eval (extract v_17712 6 8);
      v_17741 <- eval (eq v_17740 (expression.bv_nat 2 0));
      v_17742 <- eval (eq v_17740 (expression.bv_nat 2 1));
      v_17743 <- eval (eq v_17740 (expression.bv_nat 2 2));
      v_17747 <- eval (extract v_17716 224 256);
      v_17748 <- eval (extract v_17716 192 224);
      v_17749 <- eval (extract v_17716 160 192);
      v_17750 <- eval (extract v_17716 128 160);
      setRegister (lhs.of_reg v_3035) (concat (mux v_17714 v_17717 (mux v_17718 v_17719 (mux v_17720 v_17721 v_17722))) (concat (mux v_17727 v_17717 (mux v_17728 v_17719 (mux v_17729 v_17721 v_17722))) (concat (mux v_17734 v_17717 (mux v_17735 v_17719 (mux v_17736 v_17721 v_17722))) (concat (mux v_17741 v_17717 (mux v_17742 v_17719 (mux v_17743 v_17721 v_17722))) (concat (mux v_17714 v_17747 (mux v_17718 v_17748 (mux v_17720 v_17749 v_17750))) (concat (mux v_17727 v_17747 (mux v_17728 v_17748 (mux v_17729 v_17749 v_17750))) (concat (mux v_17734 v_17747 (mux v_17735 v_17748 (mux v_17736 v_17749 v_17750))) (mux v_17741 v_17747 (mux v_17742 v_17748 (mux v_17743 v_17749 v_17750))))))))));
      pure ()
    pat_end;
    pattern fun (v_3044 : Mem) (v_3045 : reg (bv 256)) (v_3046 : reg (bv 256)) => do
      v_17771 <- evaluateAddress v_3044;
      v_17772 <- load v_17771 32;
      v_17773 <- eval (extract v_17772 30 32);
      v_17775 <- getRegister v_3045;
      v_17776 <- eval (extract v_17775 96 128);
      v_17778 <- eval (extract v_17775 64 96);
      v_17780 <- eval (extract v_17775 32 64);
      v_17781 <- eval (extract v_17775 0 32);
      v_17785 <- eval (extract v_17772 62 64);
      v_17792 <- eval (extract v_17772 94 96);
      v_17799 <- eval (extract v_17772 126 128);
      v_17806 <- eval (extract v_17772 158 160);
      v_17808 <- eval (extract v_17775 224 256);
      v_17810 <- eval (extract v_17775 192 224);
      v_17812 <- eval (extract v_17775 160 192);
      v_17813 <- eval (extract v_17775 128 160);
      v_17817 <- eval (extract v_17772 190 192);
      v_17824 <- eval (extract v_17772 222 224);
      v_17831 <- eval (extract v_17772 254 256);
      setRegister (lhs.of_reg v_3046) (concat (mux (eq v_17773 (expression.bv_nat 2 0)) v_17776 (mux (eq v_17773 (expression.bv_nat 2 1)) v_17778 (mux (eq v_17773 (expression.bv_nat 2 2)) v_17780 v_17781))) (concat (mux (eq v_17785 (expression.bv_nat 2 0)) v_17776 (mux (eq v_17785 (expression.bv_nat 2 1)) v_17778 (mux (eq v_17785 (expression.bv_nat 2 2)) v_17780 v_17781))) (concat (mux (eq v_17792 (expression.bv_nat 2 0)) v_17776 (mux (eq v_17792 (expression.bv_nat 2 1)) v_17778 (mux (eq v_17792 (expression.bv_nat 2 2)) v_17780 v_17781))) (concat (mux (eq v_17799 (expression.bv_nat 2 0)) v_17776 (mux (eq v_17799 (expression.bv_nat 2 1)) v_17778 (mux (eq v_17799 (expression.bv_nat 2 2)) v_17780 v_17781))) (concat (mux (eq v_17806 (expression.bv_nat 2 0)) v_17808 (mux (eq v_17806 (expression.bv_nat 2 1)) v_17810 (mux (eq v_17806 (expression.bv_nat 2 2)) v_17812 v_17813))) (concat (mux (eq v_17817 (expression.bv_nat 2 0)) v_17808 (mux (eq v_17817 (expression.bv_nat 2 1)) v_17810 (mux (eq v_17817 (expression.bv_nat 2 2)) v_17812 v_17813))) (concat (mux (eq v_17824 (expression.bv_nat 2 0)) v_17808 (mux (eq v_17824 (expression.bv_nat 2 1)) v_17810 (mux (eq v_17824 (expression.bv_nat 2 2)) v_17812 v_17813))) (mux (eq v_17831 (expression.bv_nat 2 0)) v_17808 (mux (eq v_17831 (expression.bv_nat 2 1)) v_17810 (mux (eq v_17831 (expression.bv_nat 2 2)) v_17812 v_17813))))))))));
      pure ()
    pat_end
