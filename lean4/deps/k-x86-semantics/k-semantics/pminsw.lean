def pminsw1 : instruction :=
  definst "pminsw" $ do
    pattern fun (v_2634 : reg (bv 128)) (v_2635 : reg (bv 128)) => do
      v_5129 <- getRegister v_2635;
      v_5130 <- eval (extract v_5129 0 16);
      v_5131 <- getRegister v_2634;
      v_5132 <- eval (extract v_5131 0 16);
      v_5135 <- eval (extract v_5129 16 32);
      v_5136 <- eval (extract v_5131 16 32);
      v_5139 <- eval (extract v_5129 32 48);
      v_5140 <- eval (extract v_5131 32 48);
      v_5143 <- eval (extract v_5129 48 64);
      v_5144 <- eval (extract v_5131 48 64);
      v_5147 <- eval (extract v_5129 64 80);
      v_5148 <- eval (extract v_5131 64 80);
      v_5151 <- eval (extract v_5129 80 96);
      v_5152 <- eval (extract v_5131 80 96);
      v_5155 <- eval (extract v_5129 96 112);
      v_5156 <- eval (extract v_5131 96 112);
      v_5159 <- eval (extract v_5129 112 128);
      v_5160 <- eval (extract v_5131 112 128);
      setRegister (lhs.of_reg v_2635) (concat (mux (slt v_5130 v_5132) v_5130 v_5132) (concat (mux (slt v_5135 v_5136) v_5135 v_5136) (concat (mux (slt v_5139 v_5140) v_5139 v_5140) (concat (mux (slt v_5143 v_5144) v_5143 v_5144) (concat (mux (slt v_5147 v_5148) v_5147 v_5148) (concat (mux (slt v_5151 v_5152) v_5151 v_5152) (concat (mux (slt v_5155 v_5156) v_5155 v_5156) (mux (slt v_5159 v_5160) v_5159 v_5160))))))));
      pure ()
    pat_end;
    pattern fun (v_2630 : Mem) (v_2631 : reg (bv 128)) => do
      v_12182 <- getRegister v_2631;
      v_12183 <- eval (extract v_12182 0 16);
      v_12184 <- evaluateAddress v_2630;
      v_12185 <- load v_12184 16;
      v_12186 <- eval (extract v_12185 0 16);
      v_12189 <- eval (extract v_12182 16 32);
      v_12190 <- eval (extract v_12185 16 32);
      v_12193 <- eval (extract v_12182 32 48);
      v_12194 <- eval (extract v_12185 32 48);
      v_12197 <- eval (extract v_12182 48 64);
      v_12198 <- eval (extract v_12185 48 64);
      v_12201 <- eval (extract v_12182 64 80);
      v_12202 <- eval (extract v_12185 64 80);
      v_12205 <- eval (extract v_12182 80 96);
      v_12206 <- eval (extract v_12185 80 96);
      v_12209 <- eval (extract v_12182 96 112);
      v_12210 <- eval (extract v_12185 96 112);
      v_12213 <- eval (extract v_12182 112 128);
      v_12214 <- eval (extract v_12185 112 128);
      setRegister (lhs.of_reg v_2631) (concat (mux (slt v_12183 v_12186) v_12183 v_12186) (concat (mux (slt v_12189 v_12190) v_12189 v_12190) (concat (mux (slt v_12193 v_12194) v_12193 v_12194) (concat (mux (slt v_12197 v_12198) v_12197 v_12198) (concat (mux (slt v_12201 v_12202) v_12201 v_12202) (concat (mux (slt v_12205 v_12206) v_12205 v_12206) (concat (mux (slt v_12209 v_12210) v_12209 v_12210) (mux (slt v_12213 v_12214) v_12213 v_12214))))))));
      pure ()
    pat_end
