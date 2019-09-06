def vpminsw1 : instruction :=
  definst "vpminsw" $ do
    pattern fun (v_2587 : reg (bv 128)) (v_2588 : reg (bv 128)) (v_2589 : reg (bv 128)) => do
      v_4788 <- getRegister v_2588;
      v_4789 <- eval (extract v_4788 0 16);
      v_4790 <- getRegister v_2587;
      v_4791 <- eval (extract v_4790 0 16);
      v_4794 <- eval (extract v_4788 16 32);
      v_4795 <- eval (extract v_4790 16 32);
      v_4798 <- eval (extract v_4788 32 48);
      v_4799 <- eval (extract v_4790 32 48);
      v_4802 <- eval (extract v_4788 48 64);
      v_4803 <- eval (extract v_4790 48 64);
      v_4806 <- eval (extract v_4788 64 80);
      v_4807 <- eval (extract v_4790 64 80);
      v_4810 <- eval (extract v_4788 80 96);
      v_4811 <- eval (extract v_4790 80 96);
      v_4814 <- eval (extract v_4788 96 112);
      v_4815 <- eval (extract v_4790 96 112);
      v_4818 <- eval (extract v_4788 112 128);
      v_4819 <- eval (extract v_4790 112 128);
      setRegister (lhs.of_reg v_2589) (concat (mux (slt v_4789 v_4791) v_4789 v_4791) (concat (mux (slt v_4794 v_4795) v_4794 v_4795) (concat (mux (slt v_4798 v_4799) v_4798 v_4799) (concat (mux (slt v_4802 v_4803) v_4802 v_4803) (concat (mux (slt v_4806 v_4807) v_4806 v_4807) (concat (mux (slt v_4810 v_4811) v_4810 v_4811) (concat (mux (slt v_4814 v_4815) v_4814 v_4815) (mux (slt v_4818 v_4819) v_4818 v_4819))))))));
      pure ()
    pat_end;
    pattern fun (v_2581 : Mem) (v_2582 : reg (bv 128)) (v_2583 : reg (bv 128)) => do
      v_11445 <- getRegister v_2582;
      v_11446 <- eval (extract v_11445 0 16);
      v_11447 <- evaluateAddress v_2581;
      v_11448 <- load v_11447 16;
      v_11449 <- eval (extract v_11448 0 16);
      v_11452 <- eval (extract v_11445 16 32);
      v_11453 <- eval (extract v_11448 16 32);
      v_11456 <- eval (extract v_11445 32 48);
      v_11457 <- eval (extract v_11448 32 48);
      v_11460 <- eval (extract v_11445 48 64);
      v_11461 <- eval (extract v_11448 48 64);
      v_11464 <- eval (extract v_11445 64 80);
      v_11465 <- eval (extract v_11448 64 80);
      v_11468 <- eval (extract v_11445 80 96);
      v_11469 <- eval (extract v_11448 80 96);
      v_11472 <- eval (extract v_11445 96 112);
      v_11473 <- eval (extract v_11448 96 112);
      v_11476 <- eval (extract v_11445 112 128);
      v_11477 <- eval (extract v_11448 112 128);
      setRegister (lhs.of_reg v_2583) (concat (mux (slt v_11446 v_11449) v_11446 v_11449) (concat (mux (slt v_11452 v_11453) v_11452 v_11453) (concat (mux (slt v_11456 v_11457) v_11456 v_11457) (concat (mux (slt v_11460 v_11461) v_11460 v_11461) (concat (mux (slt v_11464 v_11465) v_11464 v_11465) (concat (mux (slt v_11468 v_11469) v_11468 v_11469) (concat (mux (slt v_11472 v_11473) v_11472 v_11473) (mux (slt v_11476 v_11477) v_11476 v_11477))))))));
      pure ()
    pat_end
