def pmaxsb1 : instruction :=
  definst "pmaxsb" $ do
    pattern fun (v_2548 : reg (bv 128)) (v_2549 : reg (bv 128)) => do
      v_4768 <- getRegister v_2549;
      v_4769 <- eval (extract v_4768 0 8);
      v_4770 <- getRegister v_2548;
      v_4771 <- eval (extract v_4770 0 8);
      v_4774 <- eval (extract v_4768 8 16);
      v_4775 <- eval (extract v_4770 8 16);
      v_4778 <- eval (extract v_4768 16 24);
      v_4779 <- eval (extract v_4770 16 24);
      v_4782 <- eval (extract v_4768 24 32);
      v_4783 <- eval (extract v_4770 24 32);
      v_4786 <- eval (extract v_4768 32 40);
      v_4787 <- eval (extract v_4770 32 40);
      v_4790 <- eval (extract v_4768 40 48);
      v_4791 <- eval (extract v_4770 40 48);
      v_4794 <- eval (extract v_4768 48 56);
      v_4795 <- eval (extract v_4770 48 56);
      v_4798 <- eval (extract v_4768 56 64);
      v_4799 <- eval (extract v_4770 56 64);
      v_4802 <- eval (extract v_4768 64 72);
      v_4803 <- eval (extract v_4770 64 72);
      v_4806 <- eval (extract v_4768 72 80);
      v_4807 <- eval (extract v_4770 72 80);
      v_4810 <- eval (extract v_4768 80 88);
      v_4811 <- eval (extract v_4770 80 88);
      v_4814 <- eval (extract v_4768 88 96);
      v_4815 <- eval (extract v_4770 88 96);
      v_4818 <- eval (extract v_4768 96 104);
      v_4819 <- eval (extract v_4770 96 104);
      v_4822 <- eval (extract v_4768 104 112);
      v_4823 <- eval (extract v_4770 104 112);
      v_4826 <- eval (extract v_4768 112 120);
      v_4827 <- eval (extract v_4770 112 120);
      v_4830 <- eval (extract v_4768 120 128);
      v_4831 <- eval (extract v_4770 120 128);
      setRegister (lhs.of_reg v_2549) (concat (mux (sgt v_4769 v_4771) v_4769 v_4771) (concat (mux (sgt v_4774 v_4775) v_4774 v_4775) (concat (mux (sgt v_4778 v_4779) v_4778 v_4779) (concat (mux (sgt v_4782 v_4783) v_4782 v_4783) (concat (mux (sgt v_4786 v_4787) v_4786 v_4787) (concat (mux (sgt v_4790 v_4791) v_4790 v_4791) (concat (mux (sgt v_4794 v_4795) v_4794 v_4795) (concat (mux (sgt v_4798 v_4799) v_4798 v_4799) (concat (mux (sgt v_4802 v_4803) v_4802 v_4803) (concat (mux (sgt v_4806 v_4807) v_4806 v_4807) (concat (mux (sgt v_4810 v_4811) v_4810 v_4811) (concat (mux (sgt v_4814 v_4815) v_4814 v_4815) (concat (mux (sgt v_4818 v_4819) v_4818 v_4819) (concat (mux (sgt v_4822 v_4823) v_4822 v_4823) (concat (mux (sgt v_4826 v_4827) v_4826 v_4827) (mux (sgt v_4830 v_4831) v_4830 v_4831))))))))))))))));
      pure ()
    pat_end;
    pattern fun (v_2543 : Mem) (v_2544 : reg (bv 128)) => do
      v_12171 <- getRegister v_2544;
      v_12172 <- eval (extract v_12171 0 8);
      v_12173 <- evaluateAddress v_2543;
      v_12174 <- load v_12173 16;
      v_12175 <- eval (extract v_12174 0 8);
      v_12178 <- eval (extract v_12171 8 16);
      v_12179 <- eval (extract v_12174 8 16);
      v_12182 <- eval (extract v_12171 16 24);
      v_12183 <- eval (extract v_12174 16 24);
      v_12186 <- eval (extract v_12171 24 32);
      v_12187 <- eval (extract v_12174 24 32);
      v_12190 <- eval (extract v_12171 32 40);
      v_12191 <- eval (extract v_12174 32 40);
      v_12194 <- eval (extract v_12171 40 48);
      v_12195 <- eval (extract v_12174 40 48);
      v_12198 <- eval (extract v_12171 48 56);
      v_12199 <- eval (extract v_12174 48 56);
      v_12202 <- eval (extract v_12171 56 64);
      v_12203 <- eval (extract v_12174 56 64);
      v_12206 <- eval (extract v_12171 64 72);
      v_12207 <- eval (extract v_12174 64 72);
      v_12210 <- eval (extract v_12171 72 80);
      v_12211 <- eval (extract v_12174 72 80);
      v_12214 <- eval (extract v_12171 80 88);
      v_12215 <- eval (extract v_12174 80 88);
      v_12218 <- eval (extract v_12171 88 96);
      v_12219 <- eval (extract v_12174 88 96);
      v_12222 <- eval (extract v_12171 96 104);
      v_12223 <- eval (extract v_12174 96 104);
      v_12226 <- eval (extract v_12171 104 112);
      v_12227 <- eval (extract v_12174 104 112);
      v_12230 <- eval (extract v_12171 112 120);
      v_12231 <- eval (extract v_12174 112 120);
      v_12234 <- eval (extract v_12171 120 128);
      v_12235 <- eval (extract v_12174 120 128);
      setRegister (lhs.of_reg v_2544) (concat (mux (sgt v_12172 v_12175) v_12172 v_12175) (concat (mux (sgt v_12178 v_12179) v_12178 v_12179) (concat (mux (sgt v_12182 v_12183) v_12182 v_12183) (concat (mux (sgt v_12186 v_12187) v_12186 v_12187) (concat (mux (sgt v_12190 v_12191) v_12190 v_12191) (concat (mux (sgt v_12194 v_12195) v_12194 v_12195) (concat (mux (sgt v_12198 v_12199) v_12198 v_12199) (concat (mux (sgt v_12202 v_12203) v_12202 v_12203) (concat (mux (sgt v_12206 v_12207) v_12206 v_12207) (concat (mux (sgt v_12210 v_12211) v_12210 v_12211) (concat (mux (sgt v_12214 v_12215) v_12214 v_12215) (concat (mux (sgt v_12218 v_12219) v_12218 v_12219) (concat (mux (sgt v_12222 v_12223) v_12222 v_12223) (concat (mux (sgt v_12226 v_12227) v_12226 v_12227) (concat (mux (sgt v_12230 v_12231) v_12230 v_12231) (mux (sgt v_12234 v_12235) v_12234 v_12235))))))))))))))));
      pure ()
    pat_end
