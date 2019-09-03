def vpminsw1 : instruction :=
  definst "vpminsw" $ do
    pattern fun (v_2507 : reg (bv 128)) (v_2508 : reg (bv 128)) (v_2509 : reg (bv 128)) => do
      v_4710 <- getRegister v_2508;
      v_4711 <- eval (extract v_4710 0 16);
      v_4712 <- getRegister v_2507;
      v_4713 <- eval (extract v_4712 0 16);
      v_4716 <- eval (extract v_4710 16 32);
      v_4717 <- eval (extract v_4712 16 32);
      v_4720 <- eval (extract v_4710 32 48);
      v_4721 <- eval (extract v_4712 32 48);
      v_4724 <- eval (extract v_4710 48 64);
      v_4725 <- eval (extract v_4712 48 64);
      v_4728 <- eval (extract v_4710 64 80);
      v_4729 <- eval (extract v_4712 64 80);
      v_4732 <- eval (extract v_4710 80 96);
      v_4733 <- eval (extract v_4712 80 96);
      v_4736 <- eval (extract v_4710 96 112);
      v_4737 <- eval (extract v_4712 96 112);
      v_4740 <- eval (extract v_4710 112 128);
      v_4741 <- eval (extract v_4712 112 128);
      setRegister (lhs.of_reg v_2509) (concat (mux (slt v_4711 v_4713) v_4711 v_4713) (concat (mux (slt v_4716 v_4717) v_4716 v_4717) (concat (mux (slt v_4720 v_4721) v_4720 v_4721) (concat (mux (slt v_4724 v_4725) v_4724 v_4725) (concat (mux (slt v_4728 v_4729) v_4728 v_4729) (concat (mux (slt v_4732 v_4733) v_4732 v_4733) (concat (mux (slt v_4736 v_4737) v_4736 v_4737) (mux (slt v_4740 v_4741) v_4740 v_4741))))))));
      pure ()
    pat_end;
    pattern fun (v_2501 : Mem) (v_2502 : reg (bv 128)) (v_2503 : reg (bv 128)) => do
      v_11623 <- getRegister v_2502;
      v_11624 <- eval (extract v_11623 0 16);
      v_11625 <- evaluateAddress v_2501;
      v_11626 <- load v_11625 16;
      v_11627 <- eval (extract v_11626 0 16);
      v_11630 <- eval (extract v_11623 16 32);
      v_11631 <- eval (extract v_11626 16 32);
      v_11634 <- eval (extract v_11623 32 48);
      v_11635 <- eval (extract v_11626 32 48);
      v_11638 <- eval (extract v_11623 48 64);
      v_11639 <- eval (extract v_11626 48 64);
      v_11642 <- eval (extract v_11623 64 80);
      v_11643 <- eval (extract v_11626 64 80);
      v_11646 <- eval (extract v_11623 80 96);
      v_11647 <- eval (extract v_11626 80 96);
      v_11650 <- eval (extract v_11623 96 112);
      v_11651 <- eval (extract v_11626 96 112);
      v_11654 <- eval (extract v_11623 112 128);
      v_11655 <- eval (extract v_11626 112 128);
      setRegister (lhs.of_reg v_2503) (concat (mux (slt v_11624 v_11627) v_11624 v_11627) (concat (mux (slt v_11630 v_11631) v_11630 v_11631) (concat (mux (slt v_11634 v_11635) v_11634 v_11635) (concat (mux (slt v_11638 v_11639) v_11638 v_11639) (concat (mux (slt v_11642 v_11643) v_11642 v_11643) (concat (mux (slt v_11646 v_11647) v_11646 v_11647) (concat (mux (slt v_11650 v_11651) v_11650 v_11651) (mux (slt v_11654 v_11655) v_11654 v_11655))))))));
      pure ()
    pat_end
