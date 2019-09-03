def vpsignb1 : instruction :=
  definst "vpsignb" $ do
    pattern fun (v_3006 : reg (bv 128)) (v_3007 : reg (bv 128)) (v_3008 : reg (bv 128)) => do
      v_7563 <- getRegister v_3006;
      v_7564 <- eval (extract v_7563 0 8);
      v_7566 <- getRegister v_3007;
      v_7567 <- eval (extract v_7566 0 8);
      v_7575 <- eval (extract v_7563 8 16);
      v_7577 <- eval (extract v_7566 8 16);
      v_7585 <- eval (extract v_7563 16 24);
      v_7587 <- eval (extract v_7566 16 24);
      v_7595 <- eval (extract v_7563 24 32);
      v_7597 <- eval (extract v_7566 24 32);
      v_7605 <- eval (extract v_7563 32 40);
      v_7607 <- eval (extract v_7566 32 40);
      v_7615 <- eval (extract v_7563 40 48);
      v_7617 <- eval (extract v_7566 40 48);
      v_7625 <- eval (extract v_7563 48 56);
      v_7627 <- eval (extract v_7566 48 56);
      v_7635 <- eval (extract v_7563 56 64);
      v_7637 <- eval (extract v_7566 56 64);
      v_7645 <- eval (extract v_7563 64 72);
      v_7647 <- eval (extract v_7566 64 72);
      v_7655 <- eval (extract v_7563 72 80);
      v_7657 <- eval (extract v_7566 72 80);
      v_7665 <- eval (extract v_7563 80 88);
      v_7667 <- eval (extract v_7566 80 88);
      v_7675 <- eval (extract v_7563 88 96);
      v_7677 <- eval (extract v_7566 88 96);
      v_7685 <- eval (extract v_7563 96 104);
      v_7687 <- eval (extract v_7566 96 104);
      v_7695 <- eval (extract v_7563 104 112);
      v_7697 <- eval (extract v_7566 104 112);
      v_7705 <- eval (extract v_7563 112 120);
      v_7707 <- eval (extract v_7566 112 120);
      v_7715 <- eval (extract v_7563 120 128);
      v_7717 <- eval (extract v_7566 120 128);
      setRegister (lhs.of_reg v_3008) (concat (mux (sgt v_7564 (expression.bv_nat 8 0)) v_7567 (mux (eq v_7564 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7567 (mi (bitwidthMInt v_7567) -1))))) (concat (mux (sgt v_7575 (expression.bv_nat 8 0)) v_7577 (mux (eq v_7575 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7577 (mi (bitwidthMInt v_7577) -1))))) (concat (mux (sgt v_7585 (expression.bv_nat 8 0)) v_7587 (mux (eq v_7585 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7587 (mi (bitwidthMInt v_7587) -1))))) (concat (mux (sgt v_7595 (expression.bv_nat 8 0)) v_7597 (mux (eq v_7595 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7597 (mi (bitwidthMInt v_7597) -1))))) (concat (mux (sgt v_7605 (expression.bv_nat 8 0)) v_7607 (mux (eq v_7605 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7607 (mi (bitwidthMInt v_7607) -1))))) (concat (mux (sgt v_7615 (expression.bv_nat 8 0)) v_7617 (mux (eq v_7615 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7617 (mi (bitwidthMInt v_7617) -1))))) (concat (mux (sgt v_7625 (expression.bv_nat 8 0)) v_7627 (mux (eq v_7625 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7627 (mi (bitwidthMInt v_7627) -1))))) (concat (mux (sgt v_7635 (expression.bv_nat 8 0)) v_7637 (mux (eq v_7635 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7637 (mi (bitwidthMInt v_7637) -1))))) (concat (mux (sgt v_7645 (expression.bv_nat 8 0)) v_7647 (mux (eq v_7645 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7647 (mi (bitwidthMInt v_7647) -1))))) (concat (mux (sgt v_7655 (expression.bv_nat 8 0)) v_7657 (mux (eq v_7655 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7657 (mi (bitwidthMInt v_7657) -1))))) (concat (mux (sgt v_7665 (expression.bv_nat 8 0)) v_7667 (mux (eq v_7665 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7667 (mi (bitwidthMInt v_7667) -1))))) (concat (mux (sgt v_7675 (expression.bv_nat 8 0)) v_7677 (mux (eq v_7675 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7677 (mi (bitwidthMInt v_7677) -1))))) (concat (mux (sgt v_7685 (expression.bv_nat 8 0)) v_7687 (mux (eq v_7685 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7687 (mi (bitwidthMInt v_7687) -1))))) (concat (mux (sgt v_7695 (expression.bv_nat 8 0)) v_7697 (mux (eq v_7695 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7697 (mi (bitwidthMInt v_7697) -1))))) (concat (mux (sgt v_7705 (expression.bv_nat 8 0)) v_7707 (mux (eq v_7705 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7707 (mi (bitwidthMInt v_7707) -1))))) (mux (sgt v_7715 (expression.bv_nat 8 0)) v_7717 (mux (eq v_7715 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_7717 (mi (bitwidthMInt v_7717) -1))))))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_3003 : Mem) (v_3001 : reg (bv 128)) (v_3002 : reg (bv 128)) => do
      v_14596 <- evaluateAddress v_3003;
      v_14597 <- load v_14596 16;
      v_14598 <- eval (extract v_14597 0 8);
      v_14600 <- getRegister v_3001;
      v_14601 <- eval (extract v_14600 0 8);
      v_14609 <- eval (extract v_14597 8 16);
      v_14611 <- eval (extract v_14600 8 16);
      v_14619 <- eval (extract v_14597 16 24);
      v_14621 <- eval (extract v_14600 16 24);
      v_14629 <- eval (extract v_14597 24 32);
      v_14631 <- eval (extract v_14600 24 32);
      v_14639 <- eval (extract v_14597 32 40);
      v_14641 <- eval (extract v_14600 32 40);
      v_14649 <- eval (extract v_14597 40 48);
      v_14651 <- eval (extract v_14600 40 48);
      v_14659 <- eval (extract v_14597 48 56);
      v_14661 <- eval (extract v_14600 48 56);
      v_14669 <- eval (extract v_14597 56 64);
      v_14671 <- eval (extract v_14600 56 64);
      v_14679 <- eval (extract v_14597 64 72);
      v_14681 <- eval (extract v_14600 64 72);
      v_14689 <- eval (extract v_14597 72 80);
      v_14691 <- eval (extract v_14600 72 80);
      v_14699 <- eval (extract v_14597 80 88);
      v_14701 <- eval (extract v_14600 80 88);
      v_14709 <- eval (extract v_14597 88 96);
      v_14711 <- eval (extract v_14600 88 96);
      v_14719 <- eval (extract v_14597 96 104);
      v_14721 <- eval (extract v_14600 96 104);
      v_14729 <- eval (extract v_14597 104 112);
      v_14731 <- eval (extract v_14600 104 112);
      v_14739 <- eval (extract v_14597 112 120);
      v_14741 <- eval (extract v_14600 112 120);
      v_14749 <- eval (extract v_14597 120 128);
      v_14751 <- eval (extract v_14600 120 128);
      setRegister (lhs.of_reg v_3002) (concat (mux (sgt v_14598 (expression.bv_nat 8 0)) v_14601 (mux (eq v_14598 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14601 (mi (bitwidthMInt v_14601) -1))))) (concat (mux (sgt v_14609 (expression.bv_nat 8 0)) v_14611 (mux (eq v_14609 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14611 (mi (bitwidthMInt v_14611) -1))))) (concat (mux (sgt v_14619 (expression.bv_nat 8 0)) v_14621 (mux (eq v_14619 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14621 (mi (bitwidthMInt v_14621) -1))))) (concat (mux (sgt v_14629 (expression.bv_nat 8 0)) v_14631 (mux (eq v_14629 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14631 (mi (bitwidthMInt v_14631) -1))))) (concat (mux (sgt v_14639 (expression.bv_nat 8 0)) v_14641 (mux (eq v_14639 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14641 (mi (bitwidthMInt v_14641) -1))))) (concat (mux (sgt v_14649 (expression.bv_nat 8 0)) v_14651 (mux (eq v_14649 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14651 (mi (bitwidthMInt v_14651) -1))))) (concat (mux (sgt v_14659 (expression.bv_nat 8 0)) v_14661 (mux (eq v_14659 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14661 (mi (bitwidthMInt v_14661) -1))))) (concat (mux (sgt v_14669 (expression.bv_nat 8 0)) v_14671 (mux (eq v_14669 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14671 (mi (bitwidthMInt v_14671) -1))))) (concat (mux (sgt v_14679 (expression.bv_nat 8 0)) v_14681 (mux (eq v_14679 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14681 (mi (bitwidthMInt v_14681) -1))))) (concat (mux (sgt v_14689 (expression.bv_nat 8 0)) v_14691 (mux (eq v_14689 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14691 (mi (bitwidthMInt v_14691) -1))))) (concat (mux (sgt v_14699 (expression.bv_nat 8 0)) v_14701 (mux (eq v_14699 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14701 (mi (bitwidthMInt v_14701) -1))))) (concat (mux (sgt v_14709 (expression.bv_nat 8 0)) v_14711 (mux (eq v_14709 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14711 (mi (bitwidthMInt v_14711) -1))))) (concat (mux (sgt v_14719 (expression.bv_nat 8 0)) v_14721 (mux (eq v_14719 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14721 (mi (bitwidthMInt v_14721) -1))))) (concat (mux (sgt v_14729 (expression.bv_nat 8 0)) v_14731 (mux (eq v_14729 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14731 (mi (bitwidthMInt v_14731) -1))))) (concat (mux (sgt v_14739 (expression.bv_nat 8 0)) v_14741 (mux (eq v_14739 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14741 (mi (bitwidthMInt v_14741) -1))))) (mux (sgt v_14749 (expression.bv_nat 8 0)) v_14751 (mux (eq v_14749 (expression.bv_nat 8 0)) (expression.bv_nat 8 0) (add (expression.bv_nat 8 1) (bv_xor v_14751 (mi (bitwidthMInt v_14751) -1))))))))))))))))))));
      pure ()
    pat_end
