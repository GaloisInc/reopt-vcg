def vpminsw1 : instruction :=
  definst "vpminsw" $ do
    pattern fun (v_2495 : reg (bv 128)) (v_2496 : reg (bv 128)) (v_2497 : reg (bv 128)) => do
      v_4697 <- getRegister v_2496;
      v_4698 <- eval (extract v_4697 0 16);
      v_4699 <- getRegister v_2495;
      v_4700 <- eval (extract v_4699 0 16);
      v_4703 <- eval (extract v_4697 16 32);
      v_4704 <- eval (extract v_4699 16 32);
      v_4707 <- eval (extract v_4697 32 48);
      v_4708 <- eval (extract v_4699 32 48);
      v_4711 <- eval (extract v_4697 48 64);
      v_4712 <- eval (extract v_4699 48 64);
      v_4715 <- eval (extract v_4697 64 80);
      v_4716 <- eval (extract v_4699 64 80);
      v_4719 <- eval (extract v_4697 80 96);
      v_4720 <- eval (extract v_4699 80 96);
      v_4723 <- eval (extract v_4697 96 112);
      v_4724 <- eval (extract v_4699 96 112);
      v_4727 <- eval (extract v_4697 112 128);
      v_4728 <- eval (extract v_4699 112 128);
      setRegister (lhs.of_reg v_2497) (concat (mux (slt v_4698 v_4700) v_4698 v_4700) (concat (mux (slt v_4703 v_4704) v_4703 v_4704) (concat (mux (slt v_4707 v_4708) v_4707 v_4708) (concat (mux (slt v_4711 v_4712) v_4711 v_4712) (concat (mux (slt v_4715 v_4716) v_4715 v_4716) (concat (mux (slt v_4719 v_4720) v_4719 v_4720) (concat (mux (slt v_4723 v_4724) v_4723 v_4724) (mux (slt v_4727 v_4728) v_4727 v_4728))))))));
      pure ()
    pat_end;
    pattern fun (v_2492 : Mem) (v_2490 : reg (bv 128)) (v_2491 : reg (bv 128)) => do
      v_12101 <- getRegister v_2490;
      v_12102 <- eval (extract v_12101 0 16);
      v_12103 <- evaluateAddress v_2492;
      v_12104 <- load v_12103 16;
      v_12105 <- eval (extract v_12104 0 16);
      v_12108 <- eval (extract v_12101 16 32);
      v_12109 <- eval (extract v_12104 16 32);
      v_12112 <- eval (extract v_12101 32 48);
      v_12113 <- eval (extract v_12104 32 48);
      v_12116 <- eval (extract v_12101 48 64);
      v_12117 <- eval (extract v_12104 48 64);
      v_12120 <- eval (extract v_12101 64 80);
      v_12121 <- eval (extract v_12104 64 80);
      v_12124 <- eval (extract v_12101 80 96);
      v_12125 <- eval (extract v_12104 80 96);
      v_12128 <- eval (extract v_12101 96 112);
      v_12129 <- eval (extract v_12104 96 112);
      v_12132 <- eval (extract v_12101 112 128);
      v_12133 <- eval (extract v_12104 112 128);
      setRegister (lhs.of_reg v_2491) (concat (mux (slt v_12102 v_12105) v_12102 v_12105) (concat (mux (slt v_12108 v_12109) v_12108 v_12109) (concat (mux (slt v_12112 v_12113) v_12112 v_12113) (concat (mux (slt v_12116 v_12117) v_12116 v_12117) (concat (mux (slt v_12120 v_12121) v_12120 v_12121) (concat (mux (slt v_12124 v_12125) v_12124 v_12125) (concat (mux (slt v_12128 v_12129) v_12128 v_12129) (mux (slt v_12132 v_12133) v_12132 v_12133))))))));
      pure ()
    pat_end
