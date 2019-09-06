def vpsignb1 : instruction :=
  definst "vpsignb" $ do
    pattern fun (v_3098 : reg (bv 128)) (v_3099 : reg (bv 128)) (v_3100 : reg (bv 128)) => do
      v_7408 <- getRegister v_3098;
      v_7409 <- eval (extract v_7408 0 8);
      v_7411 <- getRegister v_3099;
      v_7412 <- eval (extract v_7411 0 8);
      v_7418 <- eval (extract v_7408 8 16);
      v_7420 <- eval (extract v_7411 8 16);
      v_7426 <- eval (extract v_7408 16 24);
      v_7428 <- eval (extract v_7411 16 24);
      v_7434 <- eval (extract v_7408 24 32);
      v_7436 <- eval (extract v_7411 24 32);
      v_7442 <- eval (extract v_7408 32 40);
      v_7444 <- eval (extract v_7411 32 40);
      v_7450 <- eval (extract v_7408 40 48);
      v_7452 <- eval (extract v_7411 40 48);
      v_7458 <- eval (extract v_7408 48 56);
      v_7460 <- eval (extract v_7411 48 56);
      v_7466 <- eval (extract v_7408 56 64);
      v_7468 <- eval (extract v_7411 56 64);
      v_7474 <- eval (extract v_7408 64 72);
      v_7476 <- eval (extract v_7411 64 72);
      v_7482 <- eval (extract v_7408 72 80);
      v_7484 <- eval (extract v_7411 72 80);
      v_7490 <- eval (extract v_7408 80 88);
      v_7492 <- eval (extract v_7411 80 88);
      v_7498 <- eval (extract v_7408 88 96);
      v_7500 <- eval (extract v_7411 88 96);
      v_7506 <- eval (extract v_7408 96 104);
      v_7508 <- eval (extract v_7411 96 104);
      v_7514 <- eval (extract v_7408 104 112);
      v_7516 <- eval (extract v_7411 104 112);
      v_7522 <- eval (extract v_7408 112 120);
      v_7524 <- eval (extract v_7411 112 120);
      v_7530 <- eval (extract v_7408 120 128);
      v_7532 <- eval (extract v_7411 120 128);
      setRegister (lhs.of_reg v_3100) (concat (mux (sgt v_7409 (expression.bv_nat 8 0)) v_7412 (mux (eq v_7409 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7412 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7418 (expression.bv_nat 8 0)) v_7420 (mux (eq v_7418 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7420 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7426 (expression.bv_nat 8 0)) v_7428 (mux (eq v_7426 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7428 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7434 (expression.bv_nat 8 0)) v_7436 (mux (eq v_7434 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7436 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7442 (expression.bv_nat 8 0)) v_7444 (mux (eq v_7442 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7444 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7450 (expression.bv_nat 8 0)) v_7452 (mux (eq v_7450 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7452 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7458 (expression.bv_nat 8 0)) v_7460 (mux (eq v_7458 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7460 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7466 (expression.bv_nat 8 0)) v_7468 (mux (eq v_7466 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7468 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7474 (expression.bv_nat 8 0)) v_7476 (mux (eq v_7474 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7476 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7482 (expression.bv_nat 8 0)) v_7484 (mux (eq v_7482 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7484 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7490 (expression.bv_nat 8 0)) v_7492 (mux (eq v_7490 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7492 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7498 (expression.bv_nat 8 0)) v_7500 (mux (eq v_7498 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7500 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7506 (expression.bv_nat 8 0)) v_7508 (mux (eq v_7506 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7508 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7514 (expression.bv_nat 8 0)) v_7516 (mux (eq v_7514 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7516 (expression.bv_nat 8 255))))) (concat (mux (sgt v_7522 (expression.bv_nat 8 0)) v_7524 (mux (eq v_7522 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7524 (expression.bv_nat 8 255))))) (mux (sgt v_7530 (expression.bv_nat 8 0)) v_7532 (mux (eq v_7530 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7532 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3092 : Mem) (v_3093 : reg (bv 128)) (v_3094 : reg (bv 128)) => do
      v_13694 <- evaluateAddress v_3092;
      v_13695 <- load v_13694 16;
      v_13696 <- eval (extract v_13695 0 8);
      v_13698 <- getRegister v_3093;
      v_13699 <- eval (extract v_13698 0 8);
      v_13705 <- eval (extract v_13695 8 16);
      v_13707 <- eval (extract v_13698 8 16);
      v_13713 <- eval (extract v_13695 16 24);
      v_13715 <- eval (extract v_13698 16 24);
      v_13721 <- eval (extract v_13695 24 32);
      v_13723 <- eval (extract v_13698 24 32);
      v_13729 <- eval (extract v_13695 32 40);
      v_13731 <- eval (extract v_13698 32 40);
      v_13737 <- eval (extract v_13695 40 48);
      v_13739 <- eval (extract v_13698 40 48);
      v_13745 <- eval (extract v_13695 48 56);
      v_13747 <- eval (extract v_13698 48 56);
      v_13753 <- eval (extract v_13695 56 64);
      v_13755 <- eval (extract v_13698 56 64);
      v_13761 <- eval (extract v_13695 64 72);
      v_13763 <- eval (extract v_13698 64 72);
      v_13769 <- eval (extract v_13695 72 80);
      v_13771 <- eval (extract v_13698 72 80);
      v_13777 <- eval (extract v_13695 80 88);
      v_13779 <- eval (extract v_13698 80 88);
      v_13785 <- eval (extract v_13695 88 96);
      v_13787 <- eval (extract v_13698 88 96);
      v_13793 <- eval (extract v_13695 96 104);
      v_13795 <- eval (extract v_13698 96 104);
      v_13801 <- eval (extract v_13695 104 112);
      v_13803 <- eval (extract v_13698 104 112);
      v_13809 <- eval (extract v_13695 112 120);
      v_13811 <- eval (extract v_13698 112 120);
      v_13817 <- eval (extract v_13695 120 128);
      v_13819 <- eval (extract v_13698 120 128);
      setRegister (lhs.of_reg v_3094) (concat (mux (sgt v_13696 (expression.bv_nat 8 0)) v_13699 (mux (eq v_13696 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13699 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13705 (expression.bv_nat 8 0)) v_13707 (mux (eq v_13705 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13707 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13713 (expression.bv_nat 8 0)) v_13715 (mux (eq v_13713 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13715 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13721 (expression.bv_nat 8 0)) v_13723 (mux (eq v_13721 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13723 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13729 (expression.bv_nat 8 0)) v_13731 (mux (eq v_13729 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13731 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13737 (expression.bv_nat 8 0)) v_13739 (mux (eq v_13737 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13739 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13745 (expression.bv_nat 8 0)) v_13747 (mux (eq v_13745 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13747 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13753 (expression.bv_nat 8 0)) v_13755 (mux (eq v_13753 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13755 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13761 (expression.bv_nat 8 0)) v_13763 (mux (eq v_13761 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13763 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13769 (expression.bv_nat 8 0)) v_13771 (mux (eq v_13769 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13771 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13777 (expression.bv_nat 8 0)) v_13779 (mux (eq v_13777 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13779 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13785 (expression.bv_nat 8 0)) v_13787 (mux (eq v_13785 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13787 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13793 (expression.bv_nat 8 0)) v_13795 (mux (eq v_13793 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13795 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13801 (expression.bv_nat 8 0)) v_13803 (mux (eq v_13801 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13803 (expression.bv_nat 8 255))))) (concat (mux (sgt v_13809 (expression.bv_nat 8 0)) v_13811 (mux (eq v_13809 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13811 (expression.bv_nat 8 255))))) (mux (sgt v_13817 (expression.bv_nat 8 0)) v_13819 (mux (eq v_13817 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_13819 (expression.bv_nat 8 255))))))))))))))))))));
      pure ()
    pat_end
