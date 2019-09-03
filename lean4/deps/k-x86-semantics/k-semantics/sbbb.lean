def sbbb1 : instruction :=
  definst "sbbb" $ do
    pattern fun (v_3170 : imm int) al => do
      v_8173 <- getRegister cf;
      v_8175 <- eval (handleImmediateWithSignExtend v_3170 8 8);
      v_8179 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8175 (mi (bitwidthMInt v_8175) -1)));
      v_8182 <- getRegister rax;
      v_8185 <- eval (add (mux (eq v_8173 (expression.bv_nat 1 1)) v_8179 (add v_8179 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) (extract v_8182 56 64)));
      v_8190 <- eval (extract v_8185 1 2);
      v_8196 <- eval (extract v_8185 1 9);
      v_8199 <- eval (extract v_8175 0 1);
      v_8203 <- eval (eq (bv_xor v_8199 (mi (bitwidthMInt v_8199) -1)) (expression.bv_nat 1 1));
      setRegister rax (concat (extract v_8182 0 56) v_8196);
      setRegister of (mux (bit_and (eq v_8203 (eq (extract v_8182 56 57) (expression.bv_nat 1 1))) (notBool_ (eq v_8203 (eq v_8190 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8196);
      setRegister zf (zeroFlag v_8196);
      setRegister af (bv_xor (bv_xor (extract v_8175 3 4) (extract v_8182 59 60)) (extract v_8185 4 5));
      setRegister sf v_8190;
      setRegister cf (mux (notBool_ (eq (extract v_8185 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3186 : imm int) (v_3190 : reg (bv 8)) => do
      v_8233 <- getRegister cf;
      v_8235 <- eval (handleImmediateWithSignExtend v_3186 8 8);
      v_8239 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8235 (mi (bitwidthMInt v_8235) -1)));
      v_8242 <- getRegister v_3190;
      v_8244 <- eval (add (mux (eq v_8233 (expression.bv_nat 1 1)) v_8239 (add v_8239 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_8242));
      v_8249 <- eval (extract v_8244 1 2);
      v_8254 <- eval (extract v_8244 1 9);
      v_8257 <- eval (extract v_8235 0 1);
      v_8261 <- eval (eq (bv_xor v_8257 (mi (bitwidthMInt v_8257) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3190) v_8254;
      setRegister of (mux (bit_and (eq v_8261 (eq (extract v_8242 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8261 (eq v_8249 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8254);
      setRegister zf (zeroFlag v_8254);
      setRegister af (bv_xor (extract (bv_xor v_8235 v_8242) 3 4) (extract v_8244 4 5));
      setRegister sf v_8249;
      setRegister cf (mux (notBool_ (eq (extract v_8244 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3198 : reg (bv 8)) (v_3199 : reg (bv 8)) => do
      v_8281 <- getRegister cf;
      v_8283 <- getRegister v_3198;
      v_8287 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_8283 (mi (bitwidthMInt v_8283) -1)));
      v_8290 <- getRegister v_3199;
      v_8292 <- eval (add (mux (eq v_8281 (expression.bv_nat 1 1)) v_8287 (add v_8287 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_8290));
      v_8297 <- eval (extract v_8292 1 2);
      v_8302 <- eval (extract v_8292 1 9);
      v_8305 <- eval (extract v_8283 0 1);
      v_8309 <- eval (eq (bv_xor v_8305 (mi (bitwidthMInt v_8305) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3199) v_8302;
      setRegister of (mux (bit_and (eq v_8309 (eq (extract v_8290 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_8309 (eq v_8297 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_8302);
      setRegister zf (zeroFlag v_8302);
      setRegister af (bv_xor (extract (bv_xor v_8283 v_8290) 3 4) (extract v_8292 4 5));
      setRegister sf v_8297;
      setRegister cf (mux (notBool_ (eq (extract v_8292 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3191 : Mem) (v_3194 : reg (bv 8)) => do
      v_13197 <- getRegister cf;
      v_13199 <- evaluateAddress v_3191;
      v_13200 <- load v_13199 1;
      v_13204 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13200 (mi (bitwidthMInt v_13200) -1)));
      v_13207 <- getRegister v_3194;
      v_13209 <- eval (add (mux (eq v_13197 (expression.bv_nat 1 1)) v_13204 (add v_13204 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_13207));
      v_13214 <- eval (extract v_13209 1 2);
      v_13219 <- eval (extract v_13209 1 9);
      v_13222 <- eval (extract v_13200 0 1);
      v_13226 <- eval (eq (bv_xor v_13222 (mi (bitwidthMInt v_13222) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3194) v_13219;
      setRegister of (mux (bit_and (eq v_13226 (eq (extract v_13207 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13226 (eq v_13214 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13219);
      setRegister zf (zeroFlag v_13219);
      setRegister af (bv_xor (extract (bv_xor v_13200 v_13207) 3 4) (extract v_13209 4 5));
      setRegister sf v_13214;
      setRegister cf (mux (notBool_ (eq (extract v_13209 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3210 : Mem) (v_3213 : reg (bv 8)) => do
      v_13242 <- getRegister cf;
      v_13244 <- evaluateAddress v_3210;
      v_13245 <- load v_13244 1;
      v_13249 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_13245 (mi (bitwidthMInt v_13245) -1)));
      v_13252 <- getRegister v_3213;
      v_13254 <- eval (add (mux (eq v_13242 (expression.bv_nat 1 1)) v_13249 (add v_13249 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_13252));
      v_13259 <- eval (extract v_13254 1 2);
      v_13260 <- eval (extract v_13254 1 9);
      v_13267 <- eval (extract v_13245 0 1);
      v_13271 <- eval (eq (bv_xor v_13267 (mi (bitwidthMInt v_13267) -1)) (expression.bv_nat 1 1));
      setRegister (lhs.of_reg v_3213) v_13260;
      setRegister of (mux (bit_and (eq v_13271 (eq (extract v_13252 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_13271 (eq v_13259 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_13260);
      setRegister af (bv_xor (extract (bv_xor v_13245 v_13252) 3 4) (extract v_13254 4 5));
      setRegister zf (zeroFlag v_13260);
      setRegister sf v_13259;
      setRegister cf (mux (notBool_ (eq (extract v_13254 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3174 : imm int) (v_3175 : Mem) => do
      v_17743 <- evaluateAddress v_3175;
      v_17744 <- getRegister cf;
      v_17746 <- eval (handleImmediateWithSignExtend v_3174 8 8);
      v_17750 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17746 (mi (bitwidthMInt v_17746) -1)));
      v_17753 <- load v_17743 1;
      v_17755 <- eval (add (mux (eq v_17744 (expression.bv_nat 1 1)) v_17750 (add v_17750 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_17753));
      v_17756 <- eval (extract v_17755 1 9);
      store v_17743 v_17756 1;
      v_17762 <- eval (extract v_17755 1 2);
      v_17769 <- eval (extract v_17746 0 1);
      v_17773 <- eval (eq (bv_xor v_17769 (mi (bitwidthMInt v_17769) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17773 (eq (extract v_17753 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17773 (eq v_17762 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_17756);
      setRegister af (bv_xor (extract (bv_xor v_17746 v_17753) 3 4) (extract v_17755 4 5));
      setRegister zf (zeroFlag v_17756);
      setRegister sf v_17762;
      setRegister cf (mux (notBool_ (eq (extract v_17755 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end;
    pattern fun (v_3181 : reg (bv 8)) (v_3178 : Mem) => do
      v_17788 <- evaluateAddress v_3178;
      v_17789 <- getRegister cf;
      v_17791 <- getRegister v_3181;
      v_17795 <- eval (concat (expression.bv_nat 1 0) (bv_xor v_17791 (mi (bitwidthMInt v_17791) -1)));
      v_17798 <- load v_17788 1;
      v_17800 <- eval (add (mux (eq v_17789 (expression.bv_nat 1 1)) v_17795 (add v_17795 (expression.bv_nat 9 1))) (concat (expression.bv_nat 1 0) v_17798));
      v_17801 <- eval (extract v_17800 1 9);
      store v_17788 v_17801 1;
      v_17807 <- eval (extract v_17800 1 2);
      v_17814 <- eval (extract v_17791 0 1);
      v_17818 <- eval (eq (bv_xor v_17814 (mi (bitwidthMInt v_17814) -1)) (expression.bv_nat 1 1));
      setRegister of (mux (bit_and (eq v_17818 (eq (extract v_17798 0 1) (expression.bv_nat 1 1))) (notBool_ (eq v_17818 (eq v_17807 (expression.bv_nat 1 1))))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      setRegister pf (parityFlag v_17801);
      setRegister af (bv_xor (extract (bv_xor v_17791 v_17798) 3 4) (extract v_17800 4 5));
      setRegister zf (zeroFlag v_17801);
      setRegister sf v_17807;
      setRegister cf (mux (notBool_ (eq (extract v_17800 0 1) (expression.bv_nat 1 1))) (expression.bv_nat 1 1) (expression.bv_nat 1 0));
      pure ()
    pat_end
